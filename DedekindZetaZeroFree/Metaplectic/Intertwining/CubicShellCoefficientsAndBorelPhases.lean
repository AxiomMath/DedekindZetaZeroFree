module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.DeformedRootProfiles
public import DedekindZetaZeroFree.Metaplectic.Intertwining.CubicShellSupportAndIntegrability

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.RelativeBorelPhase

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPTameJacquetBruhatTests.Raw

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

theorem relative_borel_retract_actual
    (u : (LocalField F q)ˣ) (b : BL F ζ hζ q S P)
    (hb : (b : ActualCover F ζ hζ q) =
      KPPGLLocalCover.N F ζ hζ (Sum.inr q)
          (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u⁻¹ ^ (2 : ℕ))) :
    ((retractL F ζ hζ q S P b).val : ActualCover F ζ hζ q) =
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u⁻¹ ^ (2 : ℕ)) := by
  let a : actualTorus F ζ hζ q :=
    ⟨KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u⁻¹ ^ (2 : ℕ)), by
      refine ⟨KubotaRankTwo.d (LocalField F q) (u⁻¹ ^ (2 : ℕ)) 1, ?_, ?_, ?_⟩
      · rfl
      · simp [KubotaRankTwo.d]
      · simp [KubotaRankTwo.d]⟩
  let n := S.borel.upperRoot
    (Multiplicative.ofAdd (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q))
  have hn : (n : ActualCover F ζ hζ q) =
      KPPGLLocalCover.N F ζ hζ (Sum.inr q)
        (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q) :=
    (S.openCell P).upper_eq _
  have he : inBorel F ζ hζ q S P b = n * S.borel.torus a := by
    apply Subtype.ext
    change (b : ActualCover F ζ hζ q) = (n : ActualCover F ζ hζ q) * _
    rw [hb, hn, S.torus_full]
  have hr : (retractL F ζ hζ q S P b).val = a := by
    change S.borel.retract (inBorel F ζ hζ q S P b) = a
    rw [he, map_mul, S.borel.retract_upperRoot, S.borel.retract_torus, one_mul]
  exact congrArg Subtype.val hr

theorem relative_borel_weyl_retract_actual
    (hP : IsTamePolarization F ζ hζ q S P)
    (u : (LocalField F q)ˣ) (b : BL F ζ hζ q S P)
    (hb : (b : ActualCover F ζ hζ q) =
      KPPGLLocalCover.N F ζ hζ (Sum.inr q)
          (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u⁻¹ ^ (2 : ℕ))) :
    ((weylHL F ζ hζ q S P hP (retractL F ζ hζ q S P b)).val :
        ActualCover F ζ hζ q) =
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u ^ (2 : ℕ)) := by
  change (S.borel.weyl (retractL F ζ hζ q S P b).val : ActualCover F ζ hζ q) = _
  rw [← S.torus_full, S.borel.weyl_from_lift, S.torus_full,
    (S.openCell P).weyl_eq, relative_borel_retract_actual F ζ hζ q S P u b hb]
  simpa only [KPRankOneOpenCellKernel.signedWeyl,
    KPRankOneOpenCellKernel.signedWeyl_eq_prescribed_signed, KPPGLLocalCover.signedW,
    inv_pow, inv_inv] using
    ActualFiniteBorel.Geometry.signedW_conjugates_A F ζ hζ q (u⁻¹ ^ (2 : ℕ))

end DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.RelativeBorelPhase

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.RelativeBorelPhase
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPTameJacquetTestDuality KPTameTransposeLiteral KPTameTransposeKernelUnfolding

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)

private theorem relative_borel_cubic_radial_value
    (hnormalized : RawNormalizedExtension F ζ hζ q S P)
    (v : (KPTameCompact.O F q)ˣ) (y u : (LocalField F q)ˣ)
    (hu : u = KPTameCompact.unitInclusion F q v * y^3)
    (b : BL F ζ hζ q S P)
    (hb : (b : ActualCover F ζ hζ q) =
      KPPGLLocalCover.N F ζ hζ (Sum.inr q)
          (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u⁻¹ ^ (2 : ℕ))) :
    chi F ζ hζ q S P hP .minus b = normPower (LocalField F q) u (-(2/3 : ℂ)) := by
  have hp : KPPGLLocalCover.A F ζ hζ (Sum.inr q)
      (KPTameCompact.unitInclusion F q (v^2)) *
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) ((y^2)^3) =
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u^2) := by
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) _ ) *
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) _) = _
    rw [← map_mul, KPStandardLocalRootLifts.A_mul,
      ((KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.1 _ _).2]
    simp only [one_pow, map_one, one_mul]
    congr 2
    rw [hu, mul_pow, map_pow]
    simp only [← pow_mul]

  have hw := relative_borel_weyl_retract_actual F ζ hζ q S P hP u b hb
  have he : (((weylHL F ζ hζ q S P hP (retractL F ζ hζ q S P b)).val) : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) 1 *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q (v^2)) *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) ((y^2)^3) := by
    rw [map_one, one_mul, hp]
    exact hw
  have hn := hnormalized (weylHL F ζ hζ q S P hP (retractL F ζ hζ q S P b)) 1 (v^2) (y^2) he
  simp only [map_one, Units.val_one, one_mul] at hn
  rw [chi, chiH, hn]
  have hc : S.borel.coordinate (retractL F ζ hζ q S P b).val = u⁻¹ ^ (2 : ℕ) := by
    exact S.coordinate_lift _ _ (relative_borel_retract_actual F ζ hζ q S P u b hb)
  rw [hc]
  have hv : localAbs (LocalField F q) (KPTameCompact.unitInclusion F q v) = 1 := by
    have hv' : valuation (LocalField F q) (KPTameCompact.unitInclusion F q v : LocalField F q) = 1 :=
      (Valuation.integer.integers (valuation (LocalField F q))).valuation_unit v
    simp [localAbs, hv']
  have hAbs : localAbs (LocalField F q) u = localAbs (LocalField F q) (y^3) := by
    rw [hu, localAbs_mul, hv, one_mul]
  have hInv : localAbs (LocalField F q) u⁻¹ = (localAbs (LocalField F q) u)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← localAbs_mul, inv_mul_cancel, localAbs_one]
  have hPow : localAbs (LocalField F q) ((y^2)^3) = localAbs (LocalField F q) (y^3) ^ 2 := by
    rw [← pow_mul, show (2:ℕ)*3 = 3*2 by norm_num, pow_mul, pow_two, localAbs_mul, pow_two]
  simp only [normPower]
  rw [hPow, show localAbs (LocalField F q) (u⁻¹^2) = (localAbs (LocalField F q) u)⁻¹^2 by
    rw [pow_two, localAbs_mul, hInv, pow_two]]
  rw [Real.log_pow, Real.log_pow, Real.log_inv, hAbs]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eventual_negative_cubic_shell_kernel_value
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hnormalized : RawNormalizedExtension F ζ hζ q S P)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ f : scalarSections F ζ hζ q S P hP .minus,
    IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π (0, 0)) m f →
    ∀ k : ℕ, ∀ v : (KPTameCompact.O F q)ˣ, ∀ u : (LocalField F q)ˣ,
    u = KPTameCompact.unitInclusion F q v * (π⁻¹ ^ k)^3 →
    ∀ b : BL F ζ hζ q S P,
    (b : ActualCover F ζ hζ q) =
      KPPGLLocalCover.N F ζ hζ (Sum.inr q)
        (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u⁻¹ ^ (2 : ℕ)) →
    ∀ s : ℂ, ∀ x : LocalField F q,
    ((KPTameTransposeKernelUnfolding.deformedTest F ζ hζ q S P hP f s).val
      (KPRankOneShellContinuation.kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) (u : LocalField F q) *
        (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x))).val 1 =
    normPower (LocalField F q) u (2*s-2/3) *
      (DiagonalLiftGeometry.diagonalAnchorTwist F ζ hζ q S π 0 s *
        (rootLevelSet F ζ hζ q m).indicator
          (fun _ => (1 : ℂ)) (x + 1 / (u : LocalField F q))) := by
  obtain ⟨M, hM⟩ := DiagonalLiftGeometry.eventual_deformed_test_kernel_profile F ζ hζ q S P hP htame π hπ
  refine ⟨M, fun m hm f hf k v u hu b hb s x => ?_⟩
  rw [hM m hm 0 f (by simpa only [Fin.val_zero, Int.ofNat_zero] using hf) u b hb s x,
    relative_borel_cubic_radial_value F ζ hζ q S P hP hnormalized v (π⁻¹^k) u hu b hb]
  simp only [Fin.val_zero, pow_zero, Units.val_one, one_div]
  have hi : localAbs (LocalField F q) u⁻¹ = (localAbs (LocalField F q) u)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← localAbs_mul, inv_mul_cancel, localAbs_one]
  have hnp : normPower (LocalField F q) u (-(2/3 : ℂ)) *
      normPower (LocalField F q) (u⁻¹^2) (KPRankOneShellContinuation.sourceParameter .minus s) =
      normPower (LocalField F q) u (2*s-2/3) := by
    simp only [normPower, KPRankOneShellContinuation.sourceParameter]
    rw [pow_two, localAbs_mul, hi, ← pow_two, Real.log_pow, Real.log_inv, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hnp]
end DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.RelativeBorelPhase

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.RelativeBorelPhase
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPTameJacquetTestDuality KPTameTransposeLiteral KPTameTransposeKernelUnfolding
open KPRankOneRootParameter KPRankOneShellContinuation
open _root_.DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.RelativeBorelPhase renaming eventual_negative_cubic_shell_kernel_value → eventual_negative_cubic_shell_kernel_value
variable (F : Type) [Field F] [NumberField F]
 (q : HeightOneSpectrum (𝓞 F))

private theorem negative_cubic_radial_weight (π : (LocalField F q)ˣ)
 (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
   (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
 (k : ℕ) (v : (KPTameCompact.O F q)ˣ) (s : ℂ) :
 normPower (LocalField F q) (KPTameCompact.unitInclusion F q v * (π⁻¹ ^ k)^3) (2*s-2/3) =
 (residueCardinality (LocalField F q) : ℂ)⁻¹^(2*k) *
   (evaluationUnit (LocalField F q) .minus s : ℂ)^(6*k) := by
 have hAbs : localAbs (LocalField F q) (KPTameCompact.unitInclusion F q v * (π⁻¹ ^ k)^3) =
     (residueCardinality (LocalField F q) : ℝ) ^ (3*k) := by
   have hv : localAbs (LocalField F q) (KPTameCompact.unitInclusion F q v) = 1 := by
     have hv' : valuation (LocalField F q) (KPTameCompact.unitInclusion F q v : LocalField F q) = 1 :=
       (Valuation.integer.integers (valuation (LocalField F q))).valuation_unit v
     simp [localAbs, hv']
   have hp : localAbs (LocalField F q) π = (residueCardinality (LocalField F q) : ℝ)⁻¹ := by
     simp [localAbs, hπ, Real.rpow_neg_one]
   have hi : localAbs (LocalField F q) π⁻¹ = (localAbs (LocalField F q) π)⁻¹ := by
     apply eq_inv_of_mul_eq_one_left
     rw [← localAbs_mul, inv_mul_cancel, localAbs_one]
   have hpow (a : (LocalField F q)ˣ) (n : ℕ) : localAbs (LocalField F q) (a^n) = localAbs (LocalField F q) a ^ n := by
     induction n with
     | zero => simp [localAbs_one]
     | succ n hn => rw [pow_succ, localAbs_mul, hn, pow_succ]
   rw [localAbs_mul, hv, one_mul, hpow, hpow, hi, hp, inv_inv, ← pow_mul]
   congr 1
   omega
 have hq : 0 < (residueCardinality (LocalField F q) : ℝ) := by exact_mod_cast Nat.card_pos
 have hqexp : Complex.exp (Real.log (residueCardinality (LocalField F q) : ℝ)) =
     (residueCardinality (LocalField F q) : ℂ) := by
   rw [← Complex.ofReal_exp, Real.exp_log hq]
   simp
 unfold normPower
 rw [hAbs, Real.log_pow]
 change _ = _ * ((r (LocalField F q) s)⁻¹)^(6*k)
 rw [r, ← Complex.exp_neg, ← hqexp, ← Complex.exp_neg, ← Complex.exp_nat_mul,
   ← Complex.exp_nat_mul, ← Complex.exp_add]
 congr 1
 push_cast
 ring
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
 (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
 (hP : IsTamePolarization F ζ hζ q S P)

theorem eventual_negative_cubic_shell_outer_mass_value
 (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
 (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
 (hnormalized : RawNormalizedExtension F ζ hζ q S P)
 (π : (LocalField F q)ˣ)
 (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
   (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
 ∃ M : ℕ, ∀ m ≥ M, ∀ f : scalarSections F ζ hζ q S P hP .minus,
 IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π (0, 0)) m f →
 ∀ k : ℕ, ∀ v : (KPTameCompact.O F q)ˣ, ∀ u : (LocalField F q)ˣ,
 u = KPTameCompact.unitInclusion F q v * (π⁻¹ ^ k)^3 →
 ∀ b : BL F ζ hζ q S P,
 (b : ActualCover F ζ hζ q) =
   KPPGLLocalCover.N F ζ hζ (Sum.inr q) (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
   KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u⁻¹ ^ (2 : ℕ)) →
 ∀ s : ℂ,
 (∫ x in lowShell F q,
   ((deformedTest F ζ hζ q S P hP f s).val
     (kernelW (LocalField F q) S.borel .minus *
       KPPGLLocalCover.N F ζ hζ (Sum.inr q) (u : LocalField F q) *
       (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
         KPPGLLocalCover.N F ζ hζ (Sum.inr q) x))).val 1 ∂μ) =
 ((residueCardinality (LocalField F q) : ℂ)⁻¹^(2*k) *
   (evaluationUnit (LocalField F q) .minus s : ℂ)^(6*k)) *
   (DiagonalLiftGeometry.diagonalAnchorTwist F ζ hζ q S π 0 s *
     (rootMass F ζ hζ q μ m : ℂ)) := by
 obtain ⟨M, hM⟩ := eventual_negative_cubic_shell_kernel_value F ζ hζ q S P hP htame hnormalized π hπ
 obtain ⟨D, hD⟩ := KPTameJacquetBruhatTests.BruhatGeometry.eventually_actual_raw_bruhat_geometry
   F ζ hζ q S P hP htame π hπ .minus
 refine ⟨max M D, fun m hm f hf k v u hu b hb s => ?_⟩
 obtain ⟨K, hK, hc, hn, hd, hr, ho, hz, hs, hchart⟩ := hD m ((le_max_right M D).trans hm)
 have hφ : Function.support ((rootLevelSet F ζ hζ q m).indicator (fun _ => (1 : ℂ))) ⊆
     (valuation (LocalField F q)).integer := by
   intro x hx
   apply hs
   by_contra h
   exact hx (Set.indicator_of_notMem h _)
 have hp : KPCubicExpansion.valuationExponent (LocalField F q) π = 1 := by
   simp [KPCubicExpansion.valuationExponent, hπ]
 have hv : KPCubicExpansion.valuationExponent (LocalField F q) (KPTameCompact.unitInclusion F q v) = 0 :=
   KPCubicExpansion.valuationExponent_unit v
 have he : KPCubicExpansion.valuationExponent (LocalField F q) u = -(3*(k : ℤ)) := by
   rw [hu, KPCubicExpansion.valuationExponent_mul, hv, zero_add,
     ← zpow_natCast _ 3, KPCubicExpansion.valuationExponent_zpow,
     ← zpow_natCast _ k, KPCubicExpansion.valuationExponent_zpow,
     ← zpow_neg_one π, KPCubicExpansion.valuationExponent_zpow, hp]
   ring
 have hi : (u : LocalField F q)⁻¹ ∈ (valuation (LocalField F q)).integer := by
   rw [← Units.val_inv_eq_inv_val]
   rw [RootResidualGeometry.unit_mem_integer_iff_exponent_nonneg,
     ← zpow_neg_one u, KPCubicExpansion.valuationExponent_zpow, he]
   have hk : (0 : ℤ) ≤ k := Int.natCast_nonneg k
   omega
 simp_rw [hM m ((le_max_left M D).trans hm) f hf k v u hu b hb s]
 rw [show normPower (LocalField F q) u (2*s-2/3) =
     (residueCardinality (LocalField F q) : ℂ)⁻¹^(2*k) *
       (evaluationUnit (LocalField F q) .minus s : ℂ)^(6*k) by
   rw [hu]
   exact negative_cubic_radial_weight F q π hπ k v s]
 rw [integral_const_mul, integral_const_mul]
 congr 2
 change (∫ x in (valuation (LocalField F q)).integer, _ ∂μ) = _
 rw [RootResidualGeometry.integral_integer_translate_of_support (LocalField F q) μ _ hφ _ (by simpa only [one_div] using hi)]
 rw [← integral_indicator (valuation (LocalField F q)).isClosed_integer.measurableSet]
 have hind : ((valuation (LocalField F q)).integer : Set (LocalField F q)).indicator
     ((rootLevelSet F ζ hζ q m).indicator (fun _ => (1 : ℂ))) =
     (rootLevelSet F ζ hζ q m).indicator (fun _ => (1 : ℂ)) := by
   funext x
   by_cases hx : x ∈ (valuation (LocalField F q)).integer
   · simp [Set.indicator_of_mem hx]
   · have hx' : x ∉ rootLevelSet F ζ hζ q m := fun h => hx (hs h)
     simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
 have hmset : MeasurableSet (rootLevelSet F ζ hζ q m) := ho.measurableSet
 rw [hind, integral_indicator hmset]
 simp [rootMass, measureReal_def]
end DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.RelativeBorelPhase

end

end

section
noncomputable section

namespace DedekindZetaZeroFree.KPTameTransposeBaseChart.AugmentationSteps.CubeShell

open scoped NumberField Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates KPRankOneShellContinuation
open KPTameTransposeLiteral

open _root_.DedekindZetaZeroFree.KPTameValuationCoordinates renaming unit_of_exponent_zero → unit_of_exponent_zero
open _root_.DedekindZetaZeroFree.NonarchimedeanHaarScaling renaming char_abs → char_abs
open _root_.DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.RelativeBorelPhase renaming eventual_negative_cubic_shell_outer_mass_value → eventual_negative_cubic_shell_outer_mass_value
variable (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))
private theorem shell_units (π : (LocalField F q)ˣ)
 (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
 (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
 (k : ℕ) (u : LocalField F q) (hu : u ∈ expandingReverseCubeShell F q k) :
 ∃ (v : (KPTameCompact.O F q)ˣ) (w : (LocalField F q)ˣ),
 (w : LocalField F q) = u ∧ w = KPTameCompact.unitInclusion F q v * (π⁻¹ ^ k)^3 := by
 change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
  (valuation (LocalField F q) u) = WithZero.exp (3*(k : ℤ)) at hu
 have hn : u ≠ 0 := by
  intro h
  simpa [h] using hu.symm
 let w := Units.mk0 u hn
 have hw : KPCubicExpansion.valuationExponent (LocalField F q) w = -(3*(k : ℤ)) := by
  simp only [KPCubicExpansion.valuationExponent, w, Units.val_mk0, hu, WithZero.log_exp]
 have hp : KPCubicExpansion.valuationExponent (LocalField F q) π = 1 := by
  simp [KPCubicExpansion.valuationExponent, hπ]
 have hz : KPCubicExpansion.valuationExponent (LocalField F q) (w * ((π⁻¹ ^ k)^3)⁻¹) = 0 := by
  simp only [KPCubicExpansion.valuationExponent_mul, hw]
  rw [← zpow_neg_one ((π⁻¹ ^ k)^3), KPCubicExpansion.valuationExponent_zpow,
   ← zpow_natCast (π⁻¹ ^ k) 3, KPCubicExpansion.valuationExponent_zpow,
   ← zpow_natCast π⁻¹ k, KPCubicExpansion.valuationExponent_zpow,
   ← zpow_neg_one π, KPCubicExpansion.valuationExponent_zpow, hp]
  ring
 obtain ⟨v, hv⟩ := unit_of_exponent_zero (LocalField F q) _ hz
 refine ⟨v, w, rfl, ?_⟩
 change KPTameCompact.unitInclusion F q v = _ at hv
 rw [hv]
 group
private theorem integer_units_set :
 (((valuation (LocalField F q)).integer : Set (LocalField F q)) \
  ((valuation (LocalField F q)).integer.subtype '' (IsLocalRing.maximalIdeal (valuation (LocalField F q)).integer : Set (valuation (LocalField F q)).integer))) =
 {x | valuation (LocalField F q) x = 1} := by
 ext x
 simp only [Set.mem_sdiff, Set.mem_image, Set.mem_ofPred_eq]
 constructor
 · rintro ⟨hx, hn⟩
   let a : (valuation (LocalField F q)).integer := ⟨x, hx⟩
   have ha : IsUnit a := by
    by_contra h
    exact hn ⟨a, (IsLocalRing.mem_maximalIdeal a).mpr h, rfl⟩
   exact (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers (valuation (LocalField F q)))).mp ha
 · intro hx
   refine ⟨hx.le, ?_⟩
   rintro ⟨a, ha, he⟩
   have hu : IsUnit a := (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers (valuation (LocalField F q)))).mpr (he ▸ hx)
   exact (IsLocalRing.mem_maximalIdeal a).mp ha hu
private theorem shell_smul (π : (LocalField F q)ˣ)
 (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
 (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) (k : ℕ) :
 expandingReverseCubeShell F q k = ((π⁻¹ ^ k)^3) • {x | valuation (LocalField F q) x = 1} := by
 ext u
 constructor
 · intro hu
   obtain ⟨v, w, hw, he⟩ := shell_units F q π hπ k u hu
   refine ⟨(KPTameCompact.unitInclusion F q v : LocalField F q), ?_, ?_⟩
   · exact (Valuation.integer.integers (valuation (LocalField F q))).valuation_unit v
   · change (((π⁻¹ ^ k)^3 : (LocalField F q)ˣ) : LocalField F q) * _ = u
     rw [← hw, he, Units.val_mul, mul_comm]
 · rintro ⟨x, hx, rfl⟩
   change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q) (valuation (LocalField F q) (_ * x)) = _
   rw [map_mul, hx, mul_one]
   simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, map_pow, map_inv₀, hπ]
   rw [← WithZero.exp_neg, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul]
   congr 1
   simp
private theorem shell_mass (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
 (π : (LocalField F q)ˣ)
 (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
 (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) (k : ℕ) :
 μ.real (expandingReverseCubeShell F q k) = (residueCardinality (LocalField F q) : ℝ)^(3*k) *
 μ.real (((valuation (LocalField F q)).integer : Set (LocalField F q)) \
  ((valuation (LocalField F q)).integer.subtype '' (IsLocalRing.maximalIdeal (valuation (LocalField F q)).integer : Set (valuation (LocalField F q)).integer))) := by
 let := IsTopologicalAddGroup.rightUniformSpace (LocalField F q)
 have := isUniformAddGroup_of_addCommGroup (G := LocalField F q)
 have : μ.Regular := inferInstance
 rw [shell_smul F q π hπ k, measureReal_def, ← distribHaarChar_mul μ]
 simp only [ENNReal.toReal_mul, ENNReal.coe_toReal]
 rw [char_abs (LocalField F q) μ]
 have habs : KPCubicHaar.abs (LocalField F q) (↑((π⁻¹^k)^3)) = (residueCardinality (LocalField F q) : ℝ)^(3*k) := by
  simp only [KPCubicHaar.abs, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, map_pow, map_inv₀, hπ, ← WithZero.exp_neg, ← WithZero.exp_nsmul, WithZero.log_exp]
  rw [ite_eq_right (pow_ne_zero 3 (pow_ne_zero k (inv_ne_zero π.ne_zero)))]
  simp only [neg_neg, nsmul_eq_mul, mul_one, Nat.cast_ofNat]
  change (residueCardinality (LocalField F q) : ℝ) ^ (3*(k : ℤ)) = _
  norm_cast
 rw [habs, integer_units_set F q]
 rfl
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
 (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
 (hP : IsTamePolarization F ζ hζ q S P)
include hP in
private theorem relative_exists (v : (KPTameCompact.O F q)ˣ) (y u : (LocalField F q)ˣ)
 (hu : u = KPTameCompact.unitInclusion F q v * y^3) :
 ∃ b : BL F ζ hζ q S P, (b : ActualCover F ζ hζ q) =
 KPPGLLocalCover.N F ζ hζ (Sum.inr q) (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
 KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u⁻¹ ^ (2 : ℕ)) := by
 let a : actualTorus F ζ hζ q := ⟨KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u⁻¹^2), by
  refine ⟨KubotaRankTwo.d (LocalField F q) (u⁻¹^2) 1, rfl, ?_, ?_⟩ <;> simp [KubotaRankTwo.d]⟩
 have ha : a ∈ HL F ζ hζ q S P := by
  change S.heisenberg.π a ∈ P.L
  have hc : S.cubeClassEquiv (S.heisenberg.π a) ∈ P.L.map S.cubeClassEquiv.toMonoidHom := by
   rw [hP, S.cube_class, S.coordinate_lift a (u⁻¹^2) rfl]
   refine ⟨u⁻¹^2, ?_, rfl⟩
   rw [hu, mul_inv, mul_pow, ← map_inv, ← map_pow, ← inv_pow, ← pow_mul]
   apply Subgroup.mul_mem
   · exact Subgroup.mem_sup_left ⟨v⁻¹^2, rfl⟩
   · exact Subgroup.mem_sup_right ⟨y⁻¹^2, by simp [← pow_mul]⟩
  obtain ⟨d, hd, he⟩ := hc
  exact S.cubeClassEquiv.injective he ▸ hd
 let b := S.borel.upperRoot (Multiplicative.ofAdd (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q)) * S.borel.torus a
 have hb : b ∈ (HL F ζ hζ q S P).comap S.borel.retract := by
  change S.borel.retract b ∈ HL F ζ hζ q S P
  simpa [b, map_mul, S.borel.retract_upperRoot, S.borel.retract_torus] using ha
 refine ⟨⟨b.val, ⟨b, hb, rfl⟩⟩, ?_⟩
 change (b : ActualCover F ζ hζ q) = _
 simp only [b, Subgroup.coe_mul, (S.openCell P).upper_eq, S.torus_full]
 rfl

theorem eventual_baseChart_reverse_cube_shell_coefficient
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hnormalized : RawNormalizedExtension F ζ hζ q S P)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ k : ℕ, ∀ s : ℂ,
      convergenceHalfPlane .minus s →
      (∫ u in expandingReverseCubeShell F q k, ∫ x in lowShell F q,
        chartDeformedScalar F ζ hζ q S P hP
          (diagonalLift F ζ hζ q π (0, 0)) m s
          (kernelW (LocalField F q) S.borel .minus *
            KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
            (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
              KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)) ∂μ ∂μ) =
        KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry.diagonalAnchorTwist
          F ζ hζ q S π (0 : Fin 3) s *
        (((rootMass F ζ hζ q μ m : ℂ) *
          (μ.real (((valuation (LocalField F q)).integer : Set (LocalField F q)) \
            ((valuation (LocalField F q)).integer.subtype ''
              (IsLocalRing.maximalIdeal (valuation (LocalField F q)).integer :
                Set (valuation (LocalField F q)).integer))) : ℂ)) *
          ((residueCardinality (LocalField F q) : ℂ) *
            (evaluationUnit (LocalField F q) .minus s : ℂ) ^ 6) ^ k) := by
  obtain ⟨M₁, hM₁⟩ := KPTameTransposeLiteralMass.eventual_base_minus_test_exists F ζ hζ q S P hP htame π hπ
  obtain ⟨M₂, hM₂⟩ := eventual_minusTest_eq_chartDeformedScalar F ζ hζ q S P hP htame π hπ
  obtain ⟨M₃, hM₃⟩ := eventual_negative_cubic_shell_outer_mass_value F q ζ hζ S P hP μ htame hnormalized π hπ
  refine ⟨max M₁ (max M₂ M₃), fun m hm k s hs => ?_⟩
  obtain ⟨f, hf⟩ := hM₁ m ((le_max_left _ _).trans hm)
  have hm₂ := (le_max_left M₂ M₃).trans ((le_max_right M₁ _).trans hm)
  have hm₃ := (le_max_right M₂ M₃).trans ((le_max_right M₁ _).trans hm)
  have hinner : ∀ u ∈ expandingReverseCubeShell F q k,
    (∫ x in lowShell F q, chartDeformedScalar F ζ hζ q S P hP
      (diagonalLift F ζ hζ q π (0, 0)) m s
      (kernelW (LocalField F q) S.borel .minus * KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
        (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)) ∂μ) =
    ((residueCardinality (LocalField F q) : ℂ)⁻¹^(2*k) *
      (evaluationUnit (LocalField F q) .minus s : ℂ)^(6*k)) *
      (KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry.diagonalAnchorTwist F ζ hζ q S π 0 s *
        (rootMass F ζ hζ q μ m : ℂ)) := by
    intro u hu
    obtain ⟨v, w, hw, he⟩ := shell_units F q π hπ k u hu
    obtain ⟨b, hb⟩ := relative_exists F q ζ hζ S P hP v (π⁻¹^k) w he
    rw [← hw]
    simp_rw [← hM₂ m hm₂ _ f hf s]
    exact hM₃ m hm₃ f hf k v w he b hb s
  let := IsTopologicalAddGroup.rightUniformSpace (LocalField F q)
  have := isUniformAddGroup_of_addCommGroup (G := LocalField F q)
  have hmeas : MeasurableSet (expandingReverseCubeShell F q k) := by
    rw [shell_smul F q π hπ k, ← integer_units_set F q]
    apply MeasurableSet.const_smul
    exact (valuation (LocalField F q)).isClosed_integer.measurableSet.diff
      ((MeasurableEmbedding.subtype_coe (valuation (LocalField F q)).isClosed_integer.measurableSet).measurableSet_image.mpr
        (show MeasurableSet (IsLocalRing.maximalIdeal (valuation (LocalField F q)).integer : Set (valuation (LocalField F q)).integer) from (IsNoetherianRing.isClosed_ideal _).measurableSet))
  rw [setIntegral_congr_fun hmeas hinner]
  simp only [integral_const, measureReal_restrict_apply_univ, Complex.real_smul]
  rw [shell_mass F q μ π hπ k]
  push_cast
  have hq : (residueCardinality (LocalField F q) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := 𝓀[LocalField F q])).ne'
  rw [mul_pow, ← pow_mul]
  have hc : (residueCardinality (LocalField F q) : ℂ)^(3*k) *
    (residueCardinality (LocalField F q) : ℂ)⁻¹^(2*k) =
    (residueCardinality (LocalField F q) : ℂ)^k := by
    rw [show 3*k = k + 2*k by omega, pow_add, mul_assoc, ← mul_pow, mul_inv_cancel₀ hq, one_pow, mul_one]
  calc
    _ = ((residueCardinality (LocalField F q) : ℂ)^(3*k) *
        (residueCardinality (LocalField F q) : ℂ)⁻¹^(2*k)) *
      (μ.real (((valuation (LocalField F q)).integer : Set (LocalField F q)) \
        ((valuation (LocalField F q)).integer.subtype '' (IsLocalRing.maximalIdeal (valuation (LocalField F q)).integer : Set (valuation (LocalField F q)).integer))) : ℂ) *
      (evaluationUnit (LocalField F q) .minus s : ℂ)^(6*k) *
      (KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry.diagonalAnchorTwist F ζ hζ q S π 0 s *
        (rootMass F ζ hζ q μ m : ℂ)) := by ring
    _ = _ := by rw [hc]; ring

end DedekindZetaZeroFree.KPTameTransposeBaseChart.AugmentationSteps.CubeShell

end

end
