module

public import DedekindZetaZeroFree.Metaplectic.Weil.LocalSectionCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.EisensteinReferenceSections.LocalTorus
open KPGlobalTorusFiniteStages
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

 theorem finite (q : HeightOneSpectrum (𝓞 F))
    (u g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (ht : t.val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) u) :
    (LocalSeed.finite F ζ hζ P C q).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (u * g)) =
    KPLocalPrincipalSeries.deltaHalf (C.canonical q).borel
      ((C.canonical q).borel.torus t) •
    localTau F ζ hζ P C q t ((LocalSeed.finite F ζ hζ P C q).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g)) := by
  let S := C.canonical q
  let f := LocalSeed.finite F ζ hζ P C q
  have hf := f.property.1 (S.borel.torus t)
    (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g)
  change f.val (_ * _) = KPLocalPrincipalSeries.inducingScalar S.borel 0 (S.borel.torus t) •
    KPLocalStoneVonNeumann.tau (C.polarization q) (S.borel.retract (S.borel.torus t)) (f.val _) at hf
  rw [S.torus_full, ht, S.borel.retract_torus] at hf
  rw [map_mul]
  simpa only [S, f, localTau, KPLocalPrincipalSeries.inducingScalar,
    KPLocalPrincipalSeries.normPower, zero_mul, Complex.exp_zero, mul_one] using hf

 theorem arch (w : InfinitePlace F)
    (u g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) (a d : ℂˣ) (b : ℂ)
    (hu : LocalCovariance.complexMatrix F ζ hζ w u =
      KPCplxPrincipalSeriesCharts.upperTriangular a d b) :
    LocalCovariance.arch F ζ hζ w (u * g) =
      (KPCplxPrincipalSeriesCharts.inductionWeight KPCplxPrincipalSeriesCharts.positiveParameter a d : ℂ) *
      (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ u.epsilon : ℂ) *
      LocalCovariance.arch F ζ hζ w g := by
  have he : (u * g).epsilon = u.epsilon * g.epsilon := by
    rw [KPLocalCover.mul_epsilon, KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one]
  have hm : LocalCovariance.complexMatrix F ζ hζ w (u*g) =
      LocalCovariance.complexMatrix F ζ hζ w u * LocalCovariance.complexMatrix F ζ hζ w g := by
    unfold LocalCovariance.complexMatrix
    exact map_mul _ _ _
  unfold LocalCovariance.arch
  rw [he, hm, hu, (KPCplxPrincipalSeriesCharts.sphericalSection
    KPCplxPrincipalSeriesCharts.positiveParameter).property.1, map_mul, Units.val_mul]
  ring

 theorem finite_deltaHalf (q : HeightOneSpectrum (𝓞 F))
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    KPLocalPrincipalSeries.deltaHalf (C.canonical q).borel
      ((C.canonical q).borel.torus t) =
    (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate t)) (1/2 : ℝ) : ℂ) := by
  unfold KPLocalPrincipalSeries.deltaHalf
  rw [(C.canonical q).borel.retract_torus]
  have hb := congrArg (fun u : ℂˣ => (u : ℂ))
    (ProductPolarization.fullnorm_bridgefinite F q
      ((C.canonical q).borel.coordinate t))
  let y := (C.canonical q).borel.coordinate t
  have hgpos : 0 < ((KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q) y : ℝ≥0) : ℝ) := by
    exact_mod_cast KPGlobalCenterRationalCharacter.localAbs_pos F (Sum.inr q) y
  have hlpos := KPLocalPrincipalSeries.localAbs_pos (KPLocalExceptionalConstruction.LocalField F q) y
  have hbc : ((Real.rpow ((KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q) y : ℝ≥0) : ℝ) (1/6 : ℝ)) : ℂ) =
      Complex.exp ((1/6 : ℂ) * (Real.log (KPLocalPrincipalSeries.localAbs
        (KPLocalExceptionalConstruction.LocalField F q) y) : ℂ)) := hb
  have hn := congrArg norm hbc
  rw [Complex.norm_exp] at hn
  have hnorm : KPLocalPrincipalSeries.localAbs (KPLocalExceptionalConstruction.LocalField F q) y =
      ((KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q) y : ℝ≥0) : ℝ) := by
    have hh : ((KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q) y : ℝ≥0) : ℝ) ^ (1/6 : ℝ) =
        (KPLocalPrincipalSeries.localAbs (KPLocalExceptionalConstruction.LocalField F q) y) ^ (1/6 : ℝ) := by
      rw [Real.rpow_def_of_pos hlpos]
      norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hgpos _),
        Complex.mul_re, mul_comm] at hn ⊢
      exact hn
    exact ((Real.rpow_left_inj (le_of_lt hgpos) (le_of_lt hlpos)
      (by norm_num : (1/6:ℝ) ≠ 0)).mp hh).symm
  unfold KPLocalPrincipalSeries.normPower
  change Complex.exp ((1/2 : ℂ) * (Real.log (KPLocalPrincipalSeries.localAbs
    (KPLocalExceptionalConstruction.LocalField F q) y) : ℂ)) =
    ((Real.rpow ((KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q) y : ℝ≥0) : ℝ) (1/2 : ℝ)) : ℂ)
  rw [hnorm, Real.rpow_eq_pow, Real.rpow_def_of_pos hgpos]
  simp only [Complex.ofReal_exp, Complex.ofReal_mul]
  congr 1
  push_cast
  ring

end DedekindZetaZeroFree.EisensteinReferenceSections.LocalTorus

end
