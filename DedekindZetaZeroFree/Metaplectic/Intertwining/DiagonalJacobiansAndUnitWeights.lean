module

public import DedekindZetaZeroFree.Metaplectic.Torus.NormalizedResidueCharacterExtensions
public import DedekindZetaZeroFree.Metaplectic.Torus.Cubic.SignedWeylConjugation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeUnitNumeratorSteps

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates
open KPTameTransposeLiteral KPRankOneShellContinuation

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

theorem fullDiagonal_inner_increment_abs
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (u w : (KPTameCompact.O F q)ˣ) (i : Fin 3) :
    localAbs (LocalField F q)
      (π ^ ((i.val : ℤ) + 2) /
        (KPTameCompact.unitInclusion F q u * KPTameCompact.unitInclusion F q w)) =
      (residueCardinality (LocalField F q) : ℝ) ^ (-(i.val : ℤ) - 2) := by
  let A : (LocalField F q)ˣ →* ℝ :=
    { toFun := localAbs (LocalField F q)
      map_one' := localAbs_one (LocalField F q)
      map_mul' := localAbs_mul (LocalField F q) }
  have hu (x : (KPTameCompact.O F q)ˣ) :
      A (KPTameCompact.unitInclusion F q x) = 1 := by
    have hv : valuation (LocalField F q)
        (KPTameCompact.unitInclusion F q x : LocalField F q) = 1 :=
      (Valuation.integer.integers (valuation (LocalField F q))).valuation_unit x
    simp [A, localAbs, hv]
  have hp : A π = (residueCardinality (LocalField F q) : ℝ)⁻¹ := by
    simp [A, localAbs, hπ, Real.rpow_neg_one]
  change A _ = _
  rw [map_div, map_mul, hu, hu, one_mul, div_one, map_zpow, hp,
    inv_zpow, ← zpow_neg]
  congr 1
  omega

theorem normalizedExtension_unit_sheet_value
    (hnormalized : RawNormalizedExtension F ζ hζ q S P)
    (h : HL F ζ hζ q S P) (e : rootsOfUnity 3 F)
    (u : (KPTameCompact.O F q)ˣ)
    (he : (h.val : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u)) :
    (P.ωL h : ℂ) = (ordinaryIota F ζ hζ e : ℂ) := by
  have hAone : KPPGLLocalCover.A F ζ hζ (Sum.inr q) 1 = 1 := by
    have hc := S.cube_actual (1 : (LocalField F q)ˣ)
    simp only [one_pow, map_one] at hc
    exact hc.symm
  have he' : (h.val : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u) *
          KPPGLLocalCover.A F ζ hζ (Sum.inr q) ((1 : (LocalField F q)ˣ) ^ 3) := by
    simpa only [one_pow, hAone, mul_one] using he
  have hv := hnormalized h e u 1 he'
  simpa [normPower, localAbs_one] using hv

theorem normalizedExtension_unit_sheet_chiH
    (hnormalized : RawNormalizedExtension F ζ hζ q S P)
    (ε : Sign) (h : HL F ζ hζ q S P) (e : rootsOfUnity 3 F)
    (u : (KPTameCompact.O F q)ˣ)
    (he : (h.val : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u)) :
    chiH F ζ hζ q S P hP ε h = (ordinaryIota F ζ hζ e : ℂ) := by
  let c : actualTorus F ζ hζ q := (S.openCell P).centralTorus e
  have hc : (c : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e := by
    rw [← S.torus_full]
    exact (S.openCell P).central_eq e
  have ha : ((c⁻¹ * h.val : actualTorus F ζ hζ q) : ActualCover F ζ hζ q) =
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u) := by
    change (c : ActualCover F ζ hζ q)⁻¹ * (h.val : ActualCover F ζ hζ q) = _
    rw [hc, he, inv_mul_cancel_left]
  have hcoord : S.borel.coordinate h.val = KPTameCompact.unitInclusion F q u := by
    have hh := S.coordinate_lift (c⁻¹ * h.val) _ ha
    simpa only [map_mul, map_inv, c, (S.openCell P).central_coordinate e,
      inv_one, one_mul] using hh
  have hweyl : ((weylHL F ζ hζ q S P hP h).val : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u⁻¹) := by
    rw [weylHL]
    change (S.borel.weyl h.val : ActualCover F ζ hζ q) = _
    rw [← S.torus_full, S.borel.weyl_from_lift, S.torus_full,
      (S.openCell P).weyl_eq, he]
    simpa only [KPRankOneOpenCellKernel.signedWeyl,
      KPRankOneOpenCellKernel.signedWeyl_eq_prescribed_signed, KPPGLLocalCover.signedW,
      map_inv, ActualFiniteTorus.normalWord] using
      ActualFiniteBorel.Geometry.signedW_conjugates_normalWord F ζ hζ q e
        (KPTameCompact.unitInclusion F q u)
  have hv := normalizedExtension_unit_sheet_value F ζ hζ q S P hnormalized
    (weylHL F ζ hζ q S P hP h) e u⁻¹ hweyl
  have hu : localAbs (LocalField F q) (KPTameCompact.unitInclusion F q u) = 1 := by
    have hh : valuation (LocalField F q)
        (KPTameCompact.unitInclusion F q u : LocalField F q) = 1 :=
      (Valuation.integer.integers (valuation (LocalField F q))).valuation_unit u
    simp [localAbs, hh]
  cases ε with
  | plus =>
    have hp := normalizedExtension_unit_sheet_value F ζ hζ q S P hnormalized h e u he
    simp only [chiH, hp, hcoord, normPower, hu, Real.log_one, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, mul_one]
  | minus =>
    simp only [chiH, hv, hcoord, normPower, hu, Real.log_one, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, mul_one]

theorem normalizedExtension_unit_sheet_chiH_norm
    (hnormalized : RawNormalizedExtension F ζ hζ q S P)
    (ε : Sign) (h : HL F ζ hζ q S P) (e : rootsOfUnity 3 F)
    (u : (KPTameCompact.O F q)ˣ)
    (he : (h.val : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u)) :
    ‖chiH F ζ hζ q S P hP ε h‖ = 1 := by
  rw [normalizedExtension_unit_sheet_chiH F ζ hζ q S P hP hnormalized ε h e u he]
  apply Complex.norm_eq_one_of_pow_eq_one (n := 3) _ (by decide)
  have hp : e ^ 3 = 1 := Subtype.ext e.property
  have hi := congrArg (fun z : ℂˣ => (z : ℂ))
    (congrArg (ordinaryIota F ζ hζ) hp)
  simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using hi

end DedekindZetaZeroFree.KPTameTransposeUnitNumeratorSteps

end
