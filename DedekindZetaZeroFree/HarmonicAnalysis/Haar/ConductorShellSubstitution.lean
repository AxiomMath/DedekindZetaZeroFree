module

public import DedekindZetaZeroFree.Theta.Unfolding.TameTransposeKernel

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralShell

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPTameTransposeKernelUnfolding

variable (F : Type) [Field F] [NumberField F]
  (q : HeightOneSpectrum (𝓞 F))
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]

theorem conductor_shell_haar_substitution
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (g : LocalField F q → ℂ) :
    (∫ x in conductorOneShell F q π, g x ∂μ) =
      (residueCardinality (LocalField F q) : ℂ) *
        (∫ u in KPTameGauss.integerUnitShell (LocalField F q),
          g (-u / (π : LocalField F q)) ∂μ) := by
  let K := LocalField F q
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hπK : e (valuation K (π : K)) = WithZero.exp (-1 : ℤ) := hπ
  let a : K := -(π : K)
  have ha : a ≠ 0 := neg_ne_zero.mpr π.ne_zero
  have hunit : KPTameGauss.integerUnitShell K = {u | valuation K u = 1} := by
    ext u
    simp only [KPTameGauss.integerUnitShell, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, rfl, hu⟩
      exact (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp hu
    · intro hu
      exact ⟨⟨u, hu.le⟩, rfl,
        (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mpr hu⟩
  have hball (x : K) : x ∈ KPTameJacquetTestDuality.expandingBall F q π 1 ↔
      valuation K ((π : K) * x) ≤ 1 := by
    change (∃ o : 𝒪[K], x = ((π ^ 1 : Kˣ) : K)⁻¹ * o) ↔ _
    simp only [pow_one]
    constructor
    · rintro ⟨o, rfl⟩
      simpa only [← mul_assoc, mul_inv_cancel₀ π.ne_zero, one_mul] using (show valuation K (o : K) ≤ 1 from o.property)
    · intro hx
      exact ⟨⟨(π : K) * x, hx⟩, by simp [← mul_assoc]⟩
  have hpre : (fun x : K => a * x) ⁻¹' KPTameGauss.integerUnitShell K =
      conductorOneShell F q π := by
    ext x
    rw [Set.mem_preimage, hunit]
    change valuation K (a * x) = 1 ↔
      x ∈ KPTameJacquetTestDuality.expandingBall F q π 1 ∧ ¬ valuation K x ≤ 1
    rw [hball]
    have heq : valuation K (a * x) = 1 ↔ e (valuation K (a * x)) = 1 := by
      constructor
      · intro h; rw [h, map_one]
      · intro h
        apply e.injective
        change e (valuation K (a * x)) = e 1
        rwa [map_one]
    rw [heq]
    have hle : valuation K ((π : K) * x) ≤ 1 ↔
        e (valuation K ((π : K) * x)) ≤ 1 := by
      rw [← e.map_one]
      exact e.toOrderIso.le_iff_le.symm
    have hle' : valuation K x ≤ 1 ↔ e (valuation K x) ≤ 1 := by
      rw [← e.map_one]
      exact e.toOrderIso.le_iff_le.symm
    rw [hle, hle']
    simp only [a, Valuation.map_mul, Valuation.map_neg, map_mul, hπK]
    by_cases hy : e (valuation K x) = 0
    · simp [hy]
    · rw [← WithZero.exp_log hy]
      simp only [← WithZero.exp_add, WithZero.exp_eq_one,
        WithZero.exp_le_one_iff]
      omega
  have habs : IntrinsicHaarScaling.abs K a = (residueCardinality K : ℝ)⁻¹ := by
    change (if a = 0 then 0 else (IntrinsicHaarScaling.residueCard K : ℝ) ^
      WithZero.log (e (valuation K a))) = _
    rw [if_neg ha]
    have hv : e (valuation K a) = WithZero.exp (-1 : ℤ) := by
      simpa only [a, Valuation.map_neg] using hπK
    rw [hv, WithZero.log_exp, zpow_neg_one]
    rfl
  have H := (Homeomorph.mulLeft₀ a ha).measurableEmbedding.setIntegral_map
    (μ := μ) (fun u : K => g (-u / (π : K))) (KPTameGauss.integerUnitShell K)
  change (∫ u in KPTameGauss.integerUnitShell K, g (-u / (π : K))
    ∂Measure.map (fun x : K => a * x) μ) =
      ∫ x in (fun x : K => a * x) ⁻¹' KPTameGauss.integerUnitShell K,
        g (-(a * x) / (π : K)) ∂μ at H
  rw [IntrinsicHaarScaling.map_mul K μ a ha, habs,
    Measure.restrict_smul, integral_smul_measure, hpre] at H
  have hg (x : K) : -(a * x) / (π : K) = x := by
    dsimp [a]
    rw [neg_mul, neg_neg, mul_comm, mul_div_cancel_right₀ _ π.ne_zero]
  simp only [hg] at H
  rw [← H]
  have hq : 0 < (residueCardinality K : ℝ) := by
    dsimp [residueCardinality]
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField (valuation K).integer))
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (inv_nonneg.mpr hq.le), inv_inv]
  exact RCLike.real_smul_eq_coe_mul _ _

end DedekindZetaZeroFree.KPTameTransposeLiteralShell

end
