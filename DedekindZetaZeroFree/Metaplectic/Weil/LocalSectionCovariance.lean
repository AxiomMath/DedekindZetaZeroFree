module

public import DedekindZetaZeroFree.Eisenstein.Induction.LocalSphericalSections
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ComplexChartsAndSphericalSections
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.ReciprocityAndGenuineCharacterConventions

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.EisensteinReferenceSections.LocalCovariance
open KPGlobalTorusFiniteStages
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

theorem finite_upper (q : HeightOneSpectrum (𝓞 F))
    (y : KPHilbert.Completion F (Sum.inr q))
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :
    (LocalSeed.finite F ζ hζ P C q).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) y * g)) =
    (LocalSeed.finite F ζ hζ P C q).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g) := by
  let S := C.canonical q
  let f := LocalSeed.finite F ζ hζ P C q
  have hf := f.property.1 (S.borel.upperRoot (Multiplicative.ofAdd y))
    (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g)
  rw [KPLocalPrincipalSeries.upperRoot_trivial] at hf
  have hn := (S.openCell (C.polarization q)).upper_eq y
  change f.val (_ * _) = _ at hf
  rw [hn] at hf
  rw [map_mul]
  exact hf

theorem finite_scalar (q : HeightOneSpectrum (𝓞 F))
    (z : (KPHilbert.Completion F (Sum.inr q))ˣ)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :
    (LocalSeed.finite F ζ hζ P C q).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) z * g)) =
    (LocalSeed.finite F ζ hζ P C q).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g) := by
  rw [map_mul]
  have hs : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) z) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨z, rfl⟩)
  rw [hs, one_mul]

theorem finite_central (q : HeightOneSpectrum (𝓞 F)) (e : rootsOfUnity 3 F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :
    (LocalSeed.finite F ζ hζ P C q).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPLocalCover.centralInjection F ζ hζ (Sum.inr q) e * g)) =
    (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ e : ℂ) •
      (LocalSeed.finite F ζ hζ P C q).val
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g) := by
  let S := C.canonical q
  let B := S.openCell (C.polarization q)
  let f := LocalSeed.finite F ζ hζ P C q
  have hv := f.property.1 (S.borel.torus (B.centralTorus e))
    (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g)
  have hs : KPLocalPrincipalSeries.inducingScalar S.borel 0
      (S.borel.torus (B.centralTorus e)) = 1 := by
    simp [KPLocalPrincipalSeries.inducingScalar, KPLocalPrincipalSeries.deltaHalf,
      KPLocalPrincipalSeries.normPower, S.borel.retract_torus, B.central_coordinate,
      KPLocalPrincipalSeries.localAbs_one]
  change f.val (_ * _) = _ at hv
  rw [B.central_eq] at hv
  change f.val _ = KPLocalPrincipalSeries.inducingScalar S.borel 0
    (S.borel.torus (B.centralTorus e)) •
      KPLocalPrincipalSeries.borelAction S.borel (C.polarization q) .plus
        (S.borel.torus (B.centralTorus e)) (f.val _) at hv
  rw [hs, one_smul, B.genuine] at hv
  rw [map_mul]
  rw [S.openCell_ordinary (C.polarization q)] at hv
  exact hv

def complexMatrix (w : InfinitePlace F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) :
    KPCplxCharacterHaar.ComplexGL2 :=
  Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom g.g

def arch (w : InfinitePlace F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) : ℂ :=
  (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ g.epsilon : ℂ) *
    KPCplxPrincipalSeriesCharts.sphericalSection
      KPCplxPrincipalSeriesCharts.positiveParameter (complexMatrix F ζ hζ w g)

@[simp] theorem arch_one (w : InfinitePlace F) : arch F ζ hζ w 1 = 1 := by
  simp [arch, complexMatrix, KPLocalCover.one_g, KPLocalCover.one_epsilon,
    KPCplxPrincipalSeriesCharts.sphericalSection_one]

theorem arch_central (w : InfinitePlace F) (e : rootsOfUnity 3 F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) :
    arch F ζ hζ w (KPLocalCover.centralInjection F ζ hζ (Sum.inl w) e * g) =
      (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ e : ℂ) * arch F ζ hζ w g := by
  have he : (KPLocalCover.centralInjection F ζ hζ (Sum.inl w) e * g).epsilon = e * g.epsilon := by
    change e * g.epsilon * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) 1 g.g = _
    rw [KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one]
  have hm : complexMatrix F ζ hζ w (KPLocalCover.centralInjection F ζ hζ (Sum.inl w) e * g) =
      complexMatrix F ζ hζ w g := by
    unfold complexMatrix
    congr 1
    exact one_mul g.g
  simp only [arch, he, hm, map_mul, Units.val_mul]
  ring

theorem arch_upper (w : InfinitePlace F)
    (y : KPHilbert.Completion F (Sum.inl w))
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) :
    arch F ζ hζ w (KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) y * g) =
      arch F ζ hζ w g := by
  have he : (KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) y * g).epsilon = g.epsilon := by
    change 1 * g.epsilon * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) _ _ = _
    rw [KPLocalChartTopology.complex_sigmaTwo_eq_one]
    simp
  let y' := (InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)) y
  have hm : complexMatrix F ζ hζ w (KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) y * g) =
      KPCplxPrincipalSeriesCharts.upperTriangular 1 1 y' * complexMatrix F ζ hζ w g := by
    unfold complexMatrix
    change Matrix.GeneralLinearGroup.map _ (_ * g.g) = _
    rw [map_mul]
    congr 1
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPStandardLocalRootLifts.N, KubotaRankTwo.n,
        Matrix.GeneralLinearGroup.map, KPCplxPrincipalSeriesCharts.upperTriangular, y']
  unfold arch
  rw [he, hm, (KPCplxPrincipalSeriesCharts.sphericalSection
    KPCplxPrincipalSeriesCharts.positiveParameter).property.1]
  simp [KPCplxPrincipalSeriesCharts.inductionWeight, KPCplxPrincipalSeriesCharts.complexAbs]

theorem arch_scalar (w : InfinitePlace F)
    (z : (KPHilbert.Completion F (Sum.inl w))ˣ)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) :
    arch F ζ hζ w (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w) z * g) =
      arch F ζ hζ w g := by
  have he : (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w) z * g).epsilon = g.epsilon := by
    change 1 * g.epsilon * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) _ _ = _
    rw [KPLocalChartTopology.complex_sigmaTwo_eq_one]
    simp
  have hm : complexMatrix F ζ hζ w (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w) z * g) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom z) * complexMatrix F ζ hζ w g := by
    unfold complexMatrix
    change Matrix.GeneralLinearGroup.map _ (_ * g.g) = _
    rw [map_mul]
    congr 1
    apply Units.ext
    ext i j
    simp [KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift,
      KPScalarSplitCentral.scalarMatrix, KPLocalCover.sectionMap,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.GeneralLinearGroup.map,
      Matrix.diagonal, Pi.algebraMap_def]
    split_ifs <;> simp
  unfold arch
  rw [he, hm, KPCplxPrincipalSeriesCharts.central_invariance]

theorem arch_right_su2 (w : InfinitePlace F)
    (k : KPCplxCharacterHaar.ComplexSU2)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) :
    arch F ζ hζ w (g * KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
      (Matrix.GeneralLinearGroup.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom
        (KPCplxCharacterHaar.complexSU2Embedding k))) = arch F ζ hζ w g := by
  have he : (g * KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
      (Matrix.GeneralLinearGroup.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom
        (KPCplxCharacterHaar.complexSU2Embedding k))).epsilon = g.epsilon := by
    rw [KPLocalCover.mul_epsilon, KPLocalCover.sectionMap_epsilon,
      KPLocalChartTopology.complex_sigmaTwo_eq_one]
    simp
  have hm : complexMatrix F ζ hζ w (g * KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
      (Matrix.GeneralLinearGroup.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom
        (KPCplxCharacterHaar.complexSU2Embedding k))) =
      complexMatrix F ζ hζ w g * KPCplxCharacterHaar.complexSU2Embedding k := by
    unfold complexMatrix
    rw [KPLocalCover.mul_g, map_mul]
    congr 1
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map, KPLocalCover.sectionMap]
  have hs := congrArg (fun f : KPCplxPrincipalSeriesCharts.PrincipalSeries
      KPCplxPrincipalSeriesCharts.positiveParameter => f (complexMatrix F ζ hζ w g))
    (KPCplxPrincipalSeriesCharts.sphericalSection_fixed
      KPCplxPrincipalSeriesCharts.positiveParameter
      ⟨_, ⟨k, rfl⟩⟩)
  change KPCplxPrincipalSeriesCharts.sphericalSection _
    (complexMatrix F ζ hζ w g * KPCplxCharacterHaar.complexSU2Embedding k) = _ at hs
  rw [arch, arch, he, hm, hs]

end DedekindZetaZeroFree.EisensteinReferenceSections.LocalCovariance

end
