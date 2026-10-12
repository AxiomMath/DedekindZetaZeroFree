module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalCompactHolomorphicModel

@[expose] public section

open scoped Valued
open MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector
open KPLocalPrincipalSeries
noncomputable section
set_option autoImplicit false

def negativeValuationShell
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) : Set K :=
  {x | IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K x) =
    WithZero.exp ((n + 1 : ℕ) : ℤ)}

theorem integral_eq_integer_ball_of_cubic_shells
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) (H : K → ℂ) (a : ℂ)
    (hInt : Integrable H μ)
    (hBall : (∫ x in ((valuation K).integer : Set K), H x ∂μ) = a)
    (hShell : ∀ n : ℕ,
      (∫ x in negativeValuationShell K n, H x ∂μ) =
        if 3 ∣ n + 1 then
          (1 - (residueCardinality K : ℂ)⁻¹) *
            ((residueCardinality K : ℂ)⁻¹) ^ ((n + 1) / 3) * a
        else 0) :
    (∫ x, H x ∂μ) = (1 + (residueCardinality K : ℂ)⁻¹) * a := by
  classical
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hm (n : ℕ) : MeasurableSet (negativeValuationShell K n) := by
    apply IsOpen.measurableSet
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx0 : valuation K x ≠ 0 := by
      intro h
      have hh := hx
      change e (valuation K x) = WithZero.exp ((n + 1 : ℕ) : ℤ) at hh
      simp [h] at hh
    filter_upwards [(valuation K).locally_const hx0] with y hy
    change e (valuation K y) = WithZero.exp ((n + 1 : ℕ) : ℤ)
    change e (valuation K x) = WithZero.exp ((n + 1 : ℕ) : ℤ) at hx
    simpa only [hy] using hx
  have hd : Pairwise (fun n m => Disjoint (negativeValuationShell K n) (negativeValuationShell K m)) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro x hxn hxm
    have hh : WithZero.exp ((n + 1 : ℕ) : ℤ) =
        WithZero.exp ((m + 1 : ℕ) : ℤ) := hxn.symm.trans hxm
    have hh' := WithZero.exp_injective hh
    omega
  have hc : (⋃ n : ℕ, negativeValuationShell K n) =
      ((valuation K).integer : Set K)ᶜ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_compl_iff]
    change (∃ n, x ∈ negativeValuationShell K n) ↔ ¬ valuation K x ≤ 1
    rw [not_le]
    constructor
    · rintro ⟨n, hn⟩
      have he : 1 < e (valuation K x) := by
        change e (valuation K x) = WithZero.exp ((n + 1 : ℕ) : ℤ) at hn
        rw [hn, ← WithZero.exp_zero, WithZero.exp_lt_exp]
        omega
      apply (map_lt_map_iff e).mp
      simpa only [map_one] using he
    · intro hx
      have he : 1 < e (valuation K x) := by
        simpa only [map_one] using (e.strictMono hx)
      have hne : e (valuation K x) ≠ 0 := ne_of_gt (lt_trans zero_lt_one he)
      let z := WithZero.log (e (valuation K x))
      have hz : 0 < z := by
        have hh := WithZero.exp_log hne
        rw [← hh, ← WithZero.exp_zero, WithZero.exp_lt_exp] at he
        exact he
      refine ⟨z.toNat - 1, ?_⟩
      change e (valuation K x) = WithZero.exp (((z.toNat - 1) + 1 : ℕ) : ℤ)
      have hzn : (((z.toNat - 1) + 1 : ℕ) : ℤ) = z := by
        have := Int.toNat_of_nonneg (le_of_lt hz)
        omega
      rw [hzn]
      exact (WithZero.exp_log hne).symm
  let r : ℂ := (residueCardinality K : ℂ)⁻¹
  have hq : (1 : ℝ) < residueCardinality K := by
    exact_mod_cast (Finite.one_lt_card (α := 𝓀[K]))
  have hr : ‖r‖ < 1 := by
    dsimp [r]
    rw [norm_inv, Complex.norm_natCast]
    exact inv_lt_one_of_one_lt₀ hq
  have hr1 : 1 - r ≠ 0 := by
    intro h
    have he : r = 1 := by linear_combination -h
    simpa [he] using hr
  let f : ℕ → ℂ := fun n => if 3 ∣ n + 1 then (1 - r) * r ^ ((n + 1) / 3) * a else 0
  let j : ℕ → ℕ := fun k => 3 * (k + 1) - 1
  have hj : Function.Injective j := by
    intro k l h
    dsimp [j] at h
    omega
  have hf0 : ∀ n ∉ Set.range j, f n = 0 := by
    intro n hn
    dsimp [f]
    apply if_neg
    intro hdvd
    apply hn
    refine ⟨(n + 1) / 3 - 1, ?_⟩
    have hh := Nat.div_mul_cancel hdvd
    dsimp [j]
    omega
  have hfj (k : ℕ) : f (j k) = (1 - r) * r ^ (k + 1) * a := by
    have h1 : j k + 1 = 3 * (k + 1) := by dsimp [j]; omega
    have h2 : 3 ∣ j k + 1 := by rw [h1]; exact dvd_mul_right 3 (k + 1)
    simp only [f, if_pos h2, h1, Nat.mul_div_right _ (by decide : 0 < 3)]
  have hg : HasSum (fun k : ℕ => (1 - r) * r ^ (k + 1) * a) (r * a) := by
    have hh := ((hasSum_geometric_of_norm_lt_one hr).mul_left ((1 - r) * r)).mul_right a
    have hv : ((1 - r) * r * (1 - r)⁻¹) * a = r * a := by
      rw [mul_right_comm (1 - r) r, mul_inv_cancel₀ hr1, one_mul]
    rw [hv] at hh
    exact hh.congr (fun k => by simp only [pow_succ]; ring)
  have hf : HasSum f (r * a) := by
    apply (hj.hasSum_iff hf0).mp
    simpa only [Function.comp_def, hfj] using hg
  have hsum := hasSum_integral_iUnion hm hd (hInt.integrableOn)
  have hsum' : HasSum f (∫ x in ((valuation K).integer : Set K)ᶜ, H x ∂μ) := by
    simpa only [hc, hShell, f, r] using hsum
  have ht : (∫ x in ((valuation K).integer : Set K)ᶜ, H x ∂μ) = r * a :=
    hsum'.unique hf
  rw [← integral_add_compl ((valuation K).isOpen_integer.measurableSet) hInt, hBall, ht]
  change a + r * a = (1 + r) * a
  ring

end
end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector
