module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.DeformedRootProfiles
public import DedekindZetaZeroFree.Metaplectic.Intertwining.DiagonalInverseRootSupport

@[expose] public section

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates KPRankOneShellContinuation

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)

def diagonalDoubleKernel (π : (LocalField F q)ˣ) (i : Fin 3)
    (f : scalarSections F ζ hζ q S P hP .minus) (s : ℂ)
    (x u : LocalField F q) : ℂ :=
  ((deformedTest F ζ hζ q S P hP f s).val
    (kernelW (LocalField F q) S.borel .minus *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
      (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x))).val 1

def relativeBorelRootChart : Set (LocalField F q) :=
  {u | ∃ (v : (LocalField F q)ˣ), (v : LocalField F q) = u ∧
    ∃ b : BL F ζ hζ q S P, (b : ActualCover F ζ hζ q) =
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) (-(v⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (v⁻¹ ^ (2 : ℕ))}

theorem eventual_u_first_transport_of_integrable_and_chart_support
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ (i : Fin 3)
      (f₀ fᵢ : scalarSections F ζ hζ q S P hP .minus),
      IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π (0, 0)) m f₀ →
      IsMinusTest F ζ hζ q S P hP
        (diagonalLift F ζ hζ q π ((i.val : ℤ), 0)) m fᵢ →
      ∀ s : ℂ,
      Integrable (Function.uncurry (diagonalDoubleKernel F ζ hζ q S P hP π 0 f₀ s))
        ((μ.restrict (lowShell F q)).prod μ) →
      Integrable (Function.uncurry (diagonalDoubleKernel F ζ hζ q S P hP π i fᵢ s))
        ((μ.restrict (lowShell F q)).prod μ) →
      (∀ᵐ u ∂μ, u ∉ relativeBorelRootChart F ζ hζ q S P → ∀ x ∈ lowShell F q,
        diagonalDoubleKernel F ζ hζ q S P hP π 0 f₀ s x u = 0 ∧
        diagonalDoubleKernel F ζ hζ q S P hP π i fᵢ s x u = 0) →
      (∫ x in lowShell F q, ∫ u,
        diagonalDoubleKernel F ζ hζ q S P hP π i fᵢ s x u ∂μ ∂μ) =
      (evaluationUnit (LocalField F q) .minus s : ℂ) ^ (i.val : ℤ) *
        (∫ x in lowShell F q, ∫ u,
          diagonalDoubleKernel F ζ hζ q S P hP π 0 f₀ s x u ∂μ ∂μ) := by
  obtain ⟨M, hM⟩ := eventual_deformed_test_outer_mass_transport
    F ζ hζ q S P hP μ htame π hπ
  refine ⟨M, fun m hm i f₀ fᵢ hf₀ hfᵢ s hint₀ hintᵢ hsupport => ?_⟩
  rw [integral_integral_swap hintᵢ, integral_integral_swap hint₀, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hsupport] with u hu
  by_cases hc : u ∈ relativeBorelRootChart F ζ hζ q S P
  · obtain ⟨v, rfl, b, hb⟩ := hc
    simpa only [diagonalDoubleKernel,
      diagonal_deformation_eq_evaluation_monomial F q π hπ i s] using
      hM m hm i f₀ fᵢ hf₀ hfᵢ v b hb s
  · have hz := hu hc
    have hzero₀ : (∫ x in lowShell F q,
        diagonalDoubleKernel F ζ hζ q S P hP π 0 f₀ s x u ∂μ) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      exact (hz x hx).1
    have hzeroᵢ : (∫ x in lowShell F q,
        diagonalDoubleKernel F ζ hζ q S P hP π i fᵢ s x u ∂μ) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      exact (hz x hx).2
    rw [hzero₀, hzeroᵢ, mul_zero]

end DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry

end

end

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates KPRankOneShellContinuation

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

theorem diagonal_actual_support_lower_row
    (π : (LocalField F q)ˣ) (i : Fin 3) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m) (u x : LocalField F q)
    (hg : kernelW (LocalField F q) S.borel .minus *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
      (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) ∈
      testSupport F ζ hζ q S P (diagonalLift F ζ hζ q π ((i.val : ℤ), 0)) m) :
    u ≠ 0 ∧ ∃ k : KPLocalCube.Gamma F q m,
      x + (π ^ i.val : (LocalField F q)ˣ) / u = k.val 1 0 / k.val 1 1 := by
  obtain ⟨b, k, hk, hg⟩ := hg
  obtain ⟨k, rfl⟩ := hk
  obtain ⟨t, ht⟩ := S.borel.borel_decomposition (inBorel F ζ hζ q S P b)
  let B : GL (Fin 2) (LocalField F q) :=
    KubotaRankTwo.d (LocalField F q) (S.borel.coordinate (retractL F ζ hζ q S P b)) 1 *
      KubotaRankTwo.n (LocalField F q) t.toAdd
  have pb : S.borel.projection b.val = Matrix.ProjGenLinGroup.mk B := by
    have he : (inBorel F ζ hζ q S P b).val =
        (S.borel.torus (S.borel.retract (inBorel F ζ hζ q S P b)) : ActualCover F ζ hζ q) *
          (S.borel.upperRoot t : ActualCover F ζ hζ q) := congrArg Subtype.val ht
    change S.borel.projection ((inBorel F ζ hζ q S P b).val) = _
    rw [he, map_mul, S.borel.torus_projection, S.borel.upperRoot_projection, map_mul]
    rfl
  have pa : S.borel.projection (diagonalLift F ζ hζ q π ((i.val : ℤ), 0)) =
      Matrix.ProjGenLinGroup.mk
        (KubotaRankTwo.d (LocalField F q) (π ^ i.val) 1) := by
    rw [diagonalLift_index_zero_eq_eta]
    exact (S.openCell P).projection_eq _
  have pe : S.borel.projection (eta F ζ hζ q π i) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (LocalField F q) (π ^ i.val) 1) :=
    (S.openCell P).projection_eq _
  have pw : S.borel.projection (KPPGLLocalCover.W F ζ hζ (Sum.inr q)) =
      Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.weylSwap (LocalField F q)) :=
    (S.openCell P).projection_eq _
  have pn (z : LocalField F q) : S.borel.projection (KPPGLLocalCover.N F ζ hζ (Sum.inr q) z) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n (LocalField F q) z) :=
    (S.openCell P).projection_eq _
  have pk : S.borel.projection (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) k.val)) = Matrix.ProjGenLinGroup.mk k.val :=
    (S.openCell P).projection_eq _
  have pkw : S.borel.projection (kernelW (LocalField F q) S.borel .minus) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w (LocalField F q)) := by
    rw [kernelW, (S.openCell P).weyl_eq, KPRankOneOpenCellKernel.signedWeyl,
      (S.openCell P).projection_eq, KPRankOneOpenCellKernel.signedWeyl_matrix]
  have hp := congrArg S.borel.projection hg
  simp only [map_mul, pb, pa, pe, pw, pn, pk, pkw] at hp
  have hp' : Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.w (LocalField F q) * KubotaRankTwo.n (LocalField F q) u *
        KubotaRankTwo.d (LocalField F q) (π ^ i.val) 1 *
          KPStandardLocalRootLifts.weylSwap (LocalField F q) * KubotaRankTwo.n (LocalField F q) x) =
      Matrix.ProjGenLinGroup.mk
        (B * KubotaRankTwo.d (LocalField F q) (π ^ i.val) 1 *
          k.val * KPStandardLocalRootLifts.weylSwap (LocalField F q)) := by
    simpa only [map_mul, mul_assoc] using hp
  have hB10 : B 1 0 = 0 := by simp [B, Matrix.mul_apply, Fin.sum_univ_two]
  have hB11 : B 1 1 ≠ 0 := by simp [B, Matrix.mul_apply, Fin.sum_univ_two]
  have hk11 : k.val 1 1 ≠ 0 := by
    obtain ⟨r, hr⟩ := (hm.2 k.val k.property).1 1
    rw [← hr]
    exact pow_ne_zero _ r.ne_zero
  obtain ⟨hu, he⟩ := KPTameTransposeUnitNumeratorSteps.fullDiagonal_lower_row_constraint
    B k.val (π ^ i.val) (π ^ i.val) 1 u x hB10 hB11 hk11 hp'
  exact ⟨hu, k, he⟩

theorem diagonal_actual_support_residual
    (π : (LocalField F q)ˣ) (i : Fin 3) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m) (u x : LocalField F q)
    (hg : kernelW (LocalField F q) S.borel .minus *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
      (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) ∈
      testSupport F ζ hζ q S P (diagonalLift F ζ hζ q π ((i.val : ℤ), 0)) m) :
    u ≠ 0 ∧ x + (π ^ i.val : (LocalField F q)ˣ) / u ∈ rootLevelSet F ζ hζ q m := by
  obtain ⟨hu, k, hk⟩ := diagonal_actual_support_lower_row F ζ hζ q S P π i m hm u x hg
  obtain ⟨k₀, hk₀, he₀⟩ := k.property
  have hentries := (KPLocalCube.mem_integerCongruence_iff F q m k₀).mp hk₀
  have h11ideal : k₀ 1 1 - 1 ∈ KPLocalCube.maximalIdeal F q ^ m := by
    simpa using hentries 1 1
  have h10ideal : k₀ 1 0 ∈ KPLocalCube.maximalIdeal F q ^ m := by
    simpa using hentries 1 0
  have hisunit : IsUnit (k₀ 1 1) := by
    apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
    have hmem : k₀ 1 1 - 1 ∈ KPLocalCube.maximalIdeal F q :=
      Ideal.pow_le_self (by have := hm.1; omega) h11ideal
    change 1 - k₀ 1 1 ∈ KPLocalCube.maximalIdeal F q
    simpa only [neg_sub] using (KPLocalCube.maximalIdeal F q).neg_mem hmem
  obtain ⟨v, hv⟩ := hisunit
  let y : KPLocalCube.LocalIntegers F q := k₀ 1 0 * (↑v⁻¹)
  have hyideal : y ∈ KPLocalCube.maximalIdeal F q ^ m :=
    (KPLocalCube.maximalIdeal F q ^ m).mul_mem_right _ h10ideal
  have hy : (y : LocalField F q) = x + (π ^ i.val : (LocalField F q)ˣ) / u := by
    rw [hk]
    have hratio : k.val 1 0 / k.val 1 1 =
        (k₀ 1 0 : LocalField F q) / (k₀ 1 1 : LocalField F q) := by
      rw [← he₀]
      rfl
    rw [hratio, ← hv]
    change (k₀ 1 0 : LocalField F q) * ((↑v⁻¹ : KPLocalCube.LocalIntegers F q) : LocalField F q) = _
    have hinv : ((↑v⁻¹ : KPLocalCube.LocalIntegers F q) : LocalField F q) =
        ((v : KPLocalCube.LocalIntegers F q) : LocalField F q)⁻¹ :=
      Units.val_inv_eq_inv_val (Units.map (KPLocalCube.LocalIntegers F q).subtype.toMonoidHom v)
    rw [hinv, div_eq_mul_inv]
  refine ⟨hu, ?_⟩
  let n₀ : KPLocalCube.IntegerGL2 F q :=
    ⟨!![1,y;0,1], !![1,-y;0,1], by
      ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply], by
      ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply]⟩
  have hn₀ : n₀ ∈ KPLocalCube.integerCongruence F q m := by
    rw [KPLocalCube.mem_integerCongruence_iff]
    intro a b
    fin_cases a <;> fin_cases b <;> simp [n₀, hyideal]
  have hn : KubotaRankTwo.n (LocalField F q)
      (x + (π ^ i.val : (LocalField F q)ˣ) / u) ∈ KPLocalCube.Gamma F q m := by
    refine ⟨n₀, hn₀, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [n₀, KPLocalCube.integerInclusion, Matrix.GeneralLinearGroup.map_apply,
        KubotaRankTwo.n, hy]
  exact ⟨⟨_, hn⟩, rfl⟩

theorem diagonalDoubleKernel_ne_zero_support
    (hP : IsTamePolarization F ζ hζ q S P)
    (π : (LocalField F q)ˣ) (i : Fin 3) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (f : scalarSections F ζ hζ q S P hP .minus)
    (hf : IsMinusTest F ζ hζ q S P hP
      (diagonalLift F ζ hζ q π ((i.val : ℤ), 0)) m f)
    (s : ℂ) (x u : LocalField F q)
    (hne : diagonalDoubleKernel F ζ hζ q S P hP π i f s x u ≠ 0) :
    u ≠ 0 ∧ x + (π ^ i.val : (LocalField F q)ˣ) / u ∈ rootLevelSet F ζ hζ q m := by
  apply diagonal_actual_support_residual F ζ hζ q S P π i m hm u x
  exact KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation.deformedTest_support_of_minusTest
    F ζ hζ q S P hP (scalarCoordinateEquiv F ζ hζ q S P hP)
    (fun _ _ _ => rfl) _ m f hf s hne

theorem diagonalDoubleKernel_ne_zero_radial_cutoff
    (hP : IsTamePolarization F ζ hζ q S P)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (i : Fin 3) (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (hs : rootLevelSet F ζ hζ q m ⊆ (valuation (LocalField F q)).integer)
    (f : scalarSections F ζ hζ q S P hP .minus)
    (hf : IsMinusTest F ζ hζ q S P hP
      (diagonalLift F ζ hζ q π ((i.val : ℤ), 0)) m f)
    (s : ℂ) (x : LocalField F q) (hx : x ∈ lowShell F q)
    (u : (LocalField F q)ˣ)
    (hne : diagonalDoubleKernel F ζ hζ q S P hP π i f s x u ≠ 0) :
    KPCubicExpansion.valuationExponent (LocalField F q) u ≤ (i.val : ℤ) := by
  have hr := hs (diagonalDoubleKernel_ne_zero_support F ζ hζ q S P hP
    π i m hm f hf s x u hne).2
  have hratio : ((π ^ i.val * u⁻¹ : (LocalField F q)ˣ) : LocalField F q) ∈
      (valuation (LocalField F q)).integer := by
    have ht := (valuation (LocalField F q)).integer.sub_mem hr hx
    simpa only [add_sub_cancel_left, Units.val_mul, Units.val_inv_eq_inv_val,
      div_eq_mul_inv] using ht
  have he := (RootResidualGeometry.unit_mem_integer_iff_exponent_nonneg
    (LocalField F q) (π ^ i.val * u⁻¹)).mp hratio
  have hp : KPCubicExpansion.valuationExponent (LocalField F q) π = 1 := by
    simp [KPCubicExpansion.valuationExponent, hπ]
  rw [KPCubicExpansion.valuationExponent_mul,
    ← zpow_natCast π i.val, KPCubicExpansion.valuationExponent_zpow, hp,
    ← zpow_neg_one u, KPCubicExpansion.valuationExponent_zpow] at he
  omega

theorem diagonalDoubleKernel_locallyConstant
    (hP : IsTamePolarization F ζ hζ q S P)
    (π : (LocalField F q)ˣ) (i : Fin 3)
    (f : scalarSections F ζ hζ q S P hP .minus) (s : ℂ) :
    IsLocallyConstant (Function.uncurry (diagonalDoubleKernel F ζ hζ q S P hP π i f s)) := by
  let f' := deformedTest F ζ hζ q S P hP f s
  have hlc : IsLocallyConstant (fun g : ActualCover F ζ hζ q => (f'.val g).val 1) := by
    obtain ⟨J, hJ⟩ := f'.property.2
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨{z | g⁻¹ * z ∈ J},
      J.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simpa using J.one_mem
    · intro z hz
      have he := congrFun (hJ (g⁻¹ * z) hz) g
      have he' := congrArg (fun v : InducedModule P => v.val 1) he
      change (f'.val (g * (g⁻¹ * z))).val 1 = (f'.val g).val 1 at he'
      simpa only [mul_inv_cancel_left] using he'
  have hn : Continuous (KPPGLLocalCover.N F ζ hζ (Sum.inr q)) := by
    have he : KPPGLLocalCover.N F ζ hζ (Sum.inr q) =
        fun t => (S.borel.upperRoot (Multiplicative.ofAdd t) : ActualCover F ζ hζ q) := by
      funext t
      exact ((S.openCell P).upper_eq t).symm
    rw [he]
    exact continuous_subtype_val.comp (S.borel.upperRoot_continuous.comp continuous_ofAdd)
  have hc : Continuous (fun z : LocalField F q × LocalField F q =>
      kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) z.2 *
        (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) z.1)) :=
    (continuous_const.mul (hn.comp continuous_snd)).mul
      (continuous_const.mul (hn.comp continuous_fst))
  exact hlc.comp_continuous hc

theorem diagonal_actual_support_exponent_dvd
    (hP : IsTamePolarization F ζ hζ q S P)
    (π : (LocalField F q)ˣ) (i : Fin 3) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (u : (LocalField F q)ˣ) (x : LocalField F q)
    (hg : kernelW (LocalField F q) S.borel .minus *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
      (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) ∈
      testSupport F ζ hζ q S P (diagonalLift F ζ hζ q π ((i.val : ℤ), 0)) m) :
    3 ∣ KPCubicExpansion.valuationExponent (LocalField F q) u := by
  obtain ⟨b, k, hk, hg⟩ := hg
  obtain ⟨k, rfl⟩ := hk
  obtain ⟨t, ht⟩ := S.borel.borel_decomposition (inBorel F ζ hζ q S P b)
  let z := S.borel.coordinate (retractL F ζ hζ q S P b)
  have pb : S.borel.projection b.val = Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.d (LocalField F q) z 1 * KubotaRankTwo.n (LocalField F q) t.toAdd) := by
    have he : (inBorel F ζ hζ q S P b).val =
        (S.borel.torus (S.borel.retract (inBorel F ζ hζ q S P b)) : ActualCover F ζ hζ q) *
          (S.borel.upperRoot t : ActualCover F ζ hζ q) := congrArg Subtype.val ht
    change S.borel.projection ((inBorel F ζ hζ q S P b).val) = _
    rw [he, map_mul, S.borel.torus_projection, S.borel.upperRoot_projection, map_mul]
    rfl
  have pa : S.borel.projection (eta F ζ hζ q π i) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (LocalField F q) (π ^ i.val) 1) :=
    (S.openCell P).projection_eq _
  have pw : S.borel.projection (KPPGLLocalCover.W F ζ hζ (Sum.inr q)) =
      Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.weylSwap (LocalField F q)) :=
    (S.openCell P).projection_eq _
  have pn (v : LocalField F q) : S.borel.projection (KPPGLLocalCover.N F ζ hζ (Sum.inr q) v) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n (LocalField F q) v) :=
    (S.openCell P).projection_eq _
  have pk : S.borel.projection (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) k.val)) = Matrix.ProjGenLinGroup.mk k.val :=
    (S.openCell P).projection_eq _
  have pkw : S.borel.projection (kernelW (LocalField F q) S.borel .minus) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w (LocalField F q)) := by
    rw [kernelW, (S.openCell P).weyl_eq, KPRankOneOpenCellKernel.signedWeyl,
      (S.openCell P).projection_eq, KPRankOneOpenCellKernel.signedWeyl_matrix]
  rw [diagonalLift_index_zero_eq_eta] at hg
  have hp := congrArg S.borel.projection hg
  simp only [map_mul, pb, pa, pw, pn, pk, pkw] at hp
  have hp' : Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.w (LocalField F q) * KubotaRankTwo.n (LocalField F q) u *
        KubotaRankTwo.d (LocalField F q) (π ^ i.val) 1 *
          KPStandardLocalRootLifts.weylSwap (LocalField F q) * KubotaRankTwo.n (LocalField F q) x) =
      Matrix.ProjGenLinGroup.mk
        (KubotaRankTwo.d (LocalField F q) z 1 * KubotaRankTwo.n (LocalField F q) t.toAdd *
          KubotaRankTwo.d (LocalField F q) (π ^ i.val) 1 *
          k.val * KPStandardLocalRootLifts.weylSwap (LocalField F q)) := by
    simpa only [map_mul, mul_assoc] using hp
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp'
  have h10 := congrArg (fun g : GL (Fin 2) (LocalField F q) => g 1 0) hc
  simp [Matrix.mul_apply, Fin.sum_univ_two, KubotaRankTwo.w, KubotaRankTwo.n,
    KubotaRankTwo.d, KPStandardLocalRootLifts.weylSwap,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_apply] at h10
  have hd := congrArg Matrix.GeneralLinearGroup.det hc
  simp only [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hd
  have detd (v : (LocalField F q)ˣ) : Matrix.GeneralLinearGroup.det
      (KubotaRankTwo.d (LocalField F q) v 1) = v := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have detn (v : LocalField F q) : Matrix.GeneralLinearGroup.det
      (KubotaRankTwo.n (LocalField F q) v) = 1 := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have detw : Matrix.GeneralLinearGroup.det (KubotaRankTwo.w (LocalField F q)) = 1 := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, KubotaRankTwo.w, Matrix.det_fin_two]
  have detswap : Matrix.GeneralLinearGroup.det
      (KPStandardLocalRootLifts.weylSwap (LocalField F q)) = -1 := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, KPStandardLocalRootLifts.weylSwap,
      Matrix.det_fin_two]
  simp only [detd, detn, detw, detswap, one_mul, mul_one] at hd
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h10
  have hd' : c ^ 2 = z * Matrix.GeneralLinearGroup.det k.val := by
    apply mul_left_cancel (a := π ^ i.val)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hd
  obtain ⟨r, hr⟩ := (hm.2 k.val k.property).1 1
  have huc : u * c = r ^ 3 := Units.ext (h10.trans hr.symm)
  obtain ⟨d, hdv⟩ := (hm.2 k.val k.property).2
  change d ^ 3 = Matrix.GeneralLinearGroup.det k.val at hdv
  have he₁ := congrArg (KPCubicExpansion.valuationExponent (LocalField F q)) huc
  have he₂ := congrArg (KPCubicExpansion.valuationExponent (LocalField F q)) hd'
  rw [← hdv] at he₂
  simp only [KPCubicExpansion.valuationExponent_mul] at he₁ he₂
  rw [← zpow_natCast c 2, KPCubicExpansion.valuationExponent_zpow,
    ← zpow_natCast d 3, KPCubicExpansion.valuationExponent_zpow] at he₂
  rw [← zpow_natCast r 3, KPCubicExpansion.valuationExponent_zpow] at he₁
  obtain ⟨a, ha⟩ := RootResidualGeometry.tame_borel_coordinate_exponent_dvd
    F ζ hζ q S P hP b
  change KPCubicExpansion.valuationExponent (LocalField F q) z = 3 * a at ha
  apply (Int.dvd_iff_emod_eq_zero).mpr
  omega

private theorem unitCubeClasses_of_exponent_dvd
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (u : (LocalField F q)ˣ) (hu : 3 ∣ KPCubicExpansion.valuationExponent (LocalField F q) u) :
    QuotientGroup.mk' (CubicCharacters.cubes (LocalField F q)ˣ) u ∈
      unitCubeClasses (LocalField F q) := by
  obtain ⟨n, hn⟩ := hu
  let v := u * (π ^ n) ^ (-3 : ℤ)
  have hp : KPCubicExpansion.valuationExponent (LocalField F q) π = 1 := by
    simp [KPCubicExpansion.valuationExponent, hπ]
  have hv : KPCubicExpansion.valuationExponent (LocalField F q) v = 0 := by
    dsimp [v]
    rw [KPCubicExpansion.valuationExponent_mul,
      KPCubicExpansion.valuationExponent_zpow,
      KPCubicExpansion.valuationExponent_zpow, hp, hn]
    ring
  have hvv : valuation (LocalField F q) (v : LocalField F q) = 1 := by
    let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    have hnz : e (valuation (LocalField F q) (v : LocalField F q)) ≠ 0 := by
      simp [e, v.ne_zero]
    have hl : WithZero.log (e (valuation (LocalField F q) (v : LocalField F q))) = 0 := by
      change -WithZero.log (e (valuation (LocalField F q) (v : LocalField F q))) = 0 at hv
      omega
    apply e.injective
    change e (valuation (LocalField F q) (v : LocalField F q)) = e 1
    rw [map_one, ← WithZero.exp_log hnz, hl, WithZero.exp_zero]
  let v₀ : (valuation (LocalField F q)).integer := ⟨v, hvv.le⟩
  have hvunit : IsUnit v₀ :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation (LocalField F q)))).mpr hvv
  obtain ⟨w, hw⟩ := hvunit
  have he : KPRamifiedBeta.unitsInclusion (LocalField F q) w = v := by
    apply Units.ext
    exact congrArg Subtype.val hw
  have hu' : u = KPRamifiedBeta.unitsInclusion (LocalField F q) w * (π ^ n) ^ 3 := by
    rw [he]
    dsimp [v]
    simp only [zpow_neg, zpow_ofNat]
    group
  change QuotientGroup.mk' (CubicCharacters.cubes (LocalField F q)ˣ) u ∈
    ((KPRamifiedBeta.unitsInclusion (LocalField F q)).range ⊔
    CubicCharacters.cubes (LocalField F q)ˣ).map
    (QuotientGroup.mk' (CubicCharacters.cubes (LocalField F q)ˣ))
  exact ⟨u, hu' ▸ Subgroup.mul_mem_sup ⟨w, rfl⟩ ⟨π ^ n, rfl⟩, rfl⟩

private theorem relativeBorelRootChart_of_exponent_dvd
    (hP : IsTamePolarization F ζ hζ q S P)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (u : (LocalField F q)ˣ) (hu : 3 ∣ KPCubicExpansion.valuationExponent (LocalField F q) u) :
    (u : LocalField F q) ∈ relativeBorelRootChart F ζ hζ q S P := by
  let a : actualTorus F ζ hζ q :=
    ⟨KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u⁻¹ ^ (2 : ℕ)), by
      refine ⟨KubotaRankTwo.d (LocalField F q) (u⁻¹ ^ (2 : ℕ)) 1, ?_, ?_, ?_⟩
      · rfl
      · simp [KubotaRankTwo.d]
      · simp [KubotaRankTwo.d]⟩
  have ha : S.borel.coordinate a = u⁻¹ ^ (2 : ℕ) := S.coordinate_lift a _ rfl
  have hc : S.cubeClassEquiv (S.heisenberg.π a) ∈ unitCubeClasses (LocalField F q) := by
    rw [S.cube_class, ha]
    change QuotientGroup.mk' (CubicCharacters.cubes (LocalField F q)ˣ) (u⁻¹ ^ (2 : ℕ)) ∈ _
    have hcu := unitCubeClasses_of_exponent_dvd F q π hπ u hu
    simpa only [map_pow, map_inv] using
      (unitCubeClasses (LocalField F q)).pow_mem
        ((unitCubeClasses (LocalField F q)).inv_mem hcu) 2
  have hL : a ∈ HL F ζ hζ q S P := by
    rw [← hP] at hc
    obtain ⟨d, hd, he⟩ := hc
    change S.heisenberg.π a ∈ P.L
    exact S.cubeClassEquiv.injective he ▸ hd
  let b₀ : S.borel.B :=
    S.borel.upperRoot (Multiplicative.ofAdd (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q)) *
      S.borel.torus a
  have hb₀ : b₀ ∈ (HL F ζ hζ q S P).comap S.borel.retract := by
    change S.borel.retract b₀ ∈ HL F ζ hζ q S P
    dsimp [b₀]
    rw [map_mul, S.borel.retract_upperRoot, S.borel.retract_torus, one_mul]
    exact hL
  refine ⟨u, rfl, ⟨b₀, ⟨b₀, hb₀, rfl⟩⟩, ?_⟩
  change (b₀ : ActualCover F ζ hζ q) = _
  change (S.borel.upperRoot (Multiplicative.ofAdd (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q)) : ActualCover F ζ hζ q) *
    (S.borel.torus a : ActualCover F ζ hζ q) = _
  rw [S.torus_full]
  congr 1
  exact (S.openCell P).upper_eq _

theorem diagonalDoubleKernel_ne_zero_mem_relativeBorelRootChart
    (hP : IsTamePolarization F ζ hζ q S P)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (i : Fin 3) (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (f : scalarSections F ζ hζ q S P hP .minus)
    (hf : IsMinusTest F ζ hζ q S P hP
      (diagonalLift F ζ hζ q π ((i.val : ℤ), 0)) m f)
    (s : ℂ) (x u : LocalField F q)
    (hne : diagonalDoubleKernel F ζ hζ q S P hP π i f s x u ≠ 0) :
    u ∈ relativeBorelRootChart F ζ hζ q S P := by
  have hu := (diagonalDoubleKernel_ne_zero_support F ζ hζ q S P hP
    π i m hm f hf s x u hne).1
  let v := Units.mk0 u hu
  have hg := KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation.deformedTest_support_of_minusTest
    F ζ hζ q S P hP (scalarCoordinateEquiv F ζ hζ q S P hP)
    (fun _ _ _ => rfl) _ m f hf s hne
  exact relativeBorelRootChart_of_exponent_dvd F ζ hζ q S P hP π hπ v
    (diagonal_actual_support_exponent_dvd F ζ hζ q S P hP π i m hm v x hg)

theorem eventual_u_first_transport_of_integrable
    (hP : IsTamePolarization F ζ hζ q S P)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ (i : Fin 3)
      (f₀ fᵢ : scalarSections F ζ hζ q S P hP .minus),
      IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π (0, 0)) m f₀ →
      IsMinusTest F ζ hζ q S P hP
        (diagonalLift F ζ hζ q π ((i.val : ℤ), 0)) m fᵢ →
      ∀ s : ℂ,
      Integrable (Function.uncurry (diagonalDoubleKernel F ζ hζ q S P hP π 0 f₀ s))
        ((μ.restrict (lowShell F q)).prod μ) →
      Integrable (Function.uncurry (diagonalDoubleKernel F ζ hζ q S P hP π i fᵢ s))
        ((μ.restrict (lowShell F q)).prod μ) →
      (∫ x in lowShell F q, ∫ u,
        diagonalDoubleKernel F ζ hζ q S P hP π i fᵢ s x u ∂μ ∂μ) =
      (evaluationUnit (LocalField F q) .minus s : ℂ) ^ (i.val : ℤ) *
        (∫ x in lowShell F q, ∫ u,
          diagonalDoubleKernel F ζ hζ q S P hP π 0 f₀ s x u ∂μ ∂μ) := by
  obtain ⟨M, hM⟩ := eventual_u_first_transport_of_integrable_and_chart_support
    F ζ hζ q S P hP μ htame π hπ
  obtain ⟨D, hD⟩ := KPTameJacquetBruhatTests.TestConstruction.eventually_matrixChartDepth F q
  refine ⟨max M D, fun m hm i f₀ fᵢ hf₀ hfᵢ s hint₀ hintᵢ => ?_⟩
  have hdepth := hD m ((le_max_right M D).trans hm)
  apply hM m ((le_max_left M D).trans hm) i f₀ fᵢ hf₀ hfᵢ s hint₀ hintᵢ
  apply Filter.Eventually.of_forall
  intro u hu x hx
  constructor
  · by_contra h
    exact hu (diagonalDoubleKernel_ne_zero_mem_relativeBorelRootChart F ζ hζ q S P hP
      π hπ 0 m hdepth f₀ (by simpa only [Fin.val_zero, Int.ofNat_zero] using hf₀) s x u h)
  · by_contra h
    exact hu (diagonalDoubleKernel_ne_zero_mem_relativeBorelRootChart F ζ hζ q S P hP
      π hπ i m hdepth fᵢ hfᵢ s x u h)

end DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry

end

end
