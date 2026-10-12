module
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Tactic

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.HarmonicIdentity
open MeasureTheory Polynomial
open scoped BigOperators

theorem powerWeight_integrable (α : ℝ) (hα : 0 < α) :
    Integrable (fun u : ℝ => α * u ^ (α - 1))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
    (r := α - 1) (by linarith)).const_mul α
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp h

private lemma coeff_relation (n k : ℕ) :
    (k : ℝ) * (((shiftedLegendre (n+1)).coeff k : ℝ) + (shiftedLegendre n).coeff k) =
      (n+1 : ℝ) * (((shiftedLegendre (n+1)).coeff k : ℝ) - (shiftedLegendre n).coeff k) := by
  simp only [coeff_shiftedLegendre, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast]
  by_cases hk : k ≤ n+1
  · have h1 : (n.choose k : ℝ) * (n+1) = ((n+1).choose k : ℝ) * (n+1-k) := by
      exact_mod_cast Nat.choose_mul_succ_eq n k
    have h2 : ((n+k).choose n : ℝ) * (n+k+1) =
        ((n+k+1).choose (n+1) : ℝ) * (n+1) := by
      have hh : ((n+k+1 : ℕ) : ℝ) * ((n+k).choose n : ℝ) =
          ((n+k+1).choose (n+1) : ℝ) * (n+1 : ℕ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq (n+k) n
      push_cast at hh
      simpa [mul_comm] using hh
    have h3 : n + 1 + k = n + k + 1 := by omega
    rw [h3]
    linear_combination (-1 : ℝ)^k *
      (((n+k+1).choose (n+1) : ℝ) * h1 + (n.choose k : ℝ) * h2)
  · have hkn : n < k := by omega
    have hkn1 : n + 1 < k := by omega
    simp [Nat.choose_eq_zero_of_lt hkn1, Nat.choose_eq_zero_of_lt hkn]

private lemma poly_relation (n : ℕ) :
    X * derivative ((shiftedLegendre (n+1) + shiftedLegendre n).map (Int.castRingHom ℝ)) =
      C (n+1 : ℝ) * ((shiftedLegendre (n+1) - shiftedLegendre n).map (Int.castRingHom ℝ)) := by
  ext k
  cases k with
  | zero => simp [coeff_shiftedLegendre]
  | succ k =>
    simpa [coeff_derivative, coeff_shiftedLegendre, Nat.cast_add, Nat.cast_one,
      add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc] using coeff_relation n (k+1)

noncomputable def leg (n : ℕ) : ℝ[X] := (shiftedLegendre n).map (Int.castRingHom ℝ)

private lemma leg_one (n : ℕ) : (leg n).eval 1 = (-1 : ℝ)^n := by
  have h := shiftedLegendre_eval_symm n (0 : ℝ)
  have h0 : aeval (0 : ℝ) (shiftedLegendre n) = 1 := by
    simp [aeval_def, ← coeff_zero_eq_eval_zero, coeff_shiftedLegendre]
  rw [h0] at h
  simp only [sub_zero] at h
  have hh := congrArg (fun x : ℝ => (-1)^n * x) h
  simpa [aeval_def, eval₂_eq_eval_map, leg, ← mul_assoc, ← pow_add, ← two_mul,
    pow_mul] using hh.symm

private lemma leg_relation (n : ℕ) (u : ℝ) :
    u * ((leg (n+1)).derivative.eval u + (leg n).derivative.eval u) =
      (n+1 : ℝ) * ((leg (n+1)).eval u - (leg n).eval u) := by
  have h := congrArg (fun p : ℝ[X] => p.eval u) (poly_relation n)
  simpa [leg, derivative_add] using h

private lemma weight_leg_integrable (n : ℕ) (α : ℝ) (hα : 0 < α) :
    IntervalIntegrable (fun u : ℝ => α * u^(α-1) * (leg n).eval u) volume 0 1 := by
  exact ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul α).mul_continuousOn
    (leg n).continuous.continuousOn

private lemma recurrence (n : ℕ) (α : ℝ) (hα : 0 < α) :
    (α + (n+1)) * (∫ u : ℝ in 0..1, α * u^(α-1) * (leg (n+1)).eval u) =
      ((n+1)-α) * (∫ u : ℝ in 0..1, α * u^(α-1) * (leg n).eval u) := by
  let F : ℝ → ℝ := fun u => α * u^α * ((leg (n+1)).eval u + (leg n).eval u)
  let f : ℝ → ℝ := fun u =>
    (α+(n+1)) * (α * u^(α-1) * (leg (n+1)).eval u) -
    ((n+1)-α) * (α * u^(α-1) * (leg n).eval u)
  have hf : IntervalIntegrable f volume 0 1 :=
    ((weight_leg_integrable (n+1) α hα).const_mul _).sub
      ((weight_leg_integrable n α hα).const_mul _)
  have hc : ContinuousOn F (Set.Icc 0 1) := by
    exact ((continuous_const.mul (Real.continuous_rpow_const hα.le)).mul
      ((leg (n+1)).continuous.add (leg n).continuous)).continuousOn
  have hd : ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (f u) u := by
    intro u hu
    have hr := (Real.hasDerivAt_rpow_const (p := α) (Or.inl (ne_of_gt hu.1)))
    have h := (hr.const_mul α).mul
      (((leg (n+1)).hasDerivAt u).add ((leg n).hasDerivAt u))
    convert h using 1
    have hp : u^α = u^(α-1) * u := by
      calc
        u^α = u^((α-1)+1) := by congr 1; ring
        _ = u^(α-1) * u^((1 : ℝ)) := Real.rpow_add hu.1 _ _
        _ = u^(α-1) * u := by rw [Real.rpow_one]
    dsimp [f]
    rw [hp]
    linear_combination -α * u^(α-1) * leg_relation n u
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1) hc hd hf
  have he : F 1 - F 0 = 0 := by
    simp [F, leg_one, Real.zero_rpow (ne_of_gt hα), pow_succ]
  rw [he] at hi
  dsimp [f] at hi
  rw [intervalIntegral.integral_sub
    ((weight_leg_integrable (n+1) α hα).const_mul _)
    ((weight_leg_integrable n α hα).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  linarith

private lemma integral_formula (n : ℕ) (α : ℝ) (hα : 0 < α) :
    (∫ u : ℝ in 0..1, α * u^(α-1) * (leg n).eval u) =
      ∏ j ∈ Finset.Icc 1 n, (((j : ℝ)-α)/((j : ℝ)+α)) := by
  induction n with
  | zero =>
    have hl : leg 0 = 1 := by simp [leg, shiftedLegendre]
    simp only [hl, eval_one, mul_one, intervalIntegral.integral_const_mul]
    rw [_root_.integral_rpow (Or.inl (by linarith))]
    simp [Real.zero_rpow (ne_of_gt hα), ne_of_gt hα]
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ← ih]
    have hr := recurrence n α hα
    have hn : (α+(n+1) : ℝ) ≠ 0 := by positivity
    apply (mul_left_cancel₀ hn)
    rw [hr]
    push_cast
    field_simp
    <;> ring

theorem shiftedLegendre_beta (ℓ : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    (∫ u : ℝ in Set.Icc 0 1,
      (α * u ^ (α - 1)) *
        (Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u) =
      ∏ j ∈ Finset.Icc 1 ℓ, (((j : ℝ) - α) / ((j : ℝ) + α)) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  simpa only [leg, eval₂_eq_eval_map] using integral_formula ℓ α hα

end DedekindZetaZeroFree.ComplexFractionalInverse.HarmonicIdentity
