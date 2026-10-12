module

public import DedekindZetaZeroFree.LargeSieve.Exponents.ExponentOneByApproximation

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonComparison.lean.
-/

namespace DedekindZetaZeroFree.LargeSieve

noncomputable def bootstrapExponent (n : ℕ) : ℝ := 1 + 1 / ((n : ℝ) + 1)

theorem bootstrapExponent_bounds (n : ℕ) :
    1 < bootstrapExponent n ∧ bootstrapExponent n ≤ 2 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  constructor
  · rw [bootstrapExponent]
    have : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hpos
    linarith
  · rw [bootstrapExponent]
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hpos]; linarith
    linarith

@[simp] theorem bootstrapExponent_zero : bootstrapExponent 0 = 2 := by
  norm_num [bootstrapExponent]

theorem bootstrapExponent_succ (n : ℕ) :
    bootstrapExponent (n + 1) = 2 - 1 / bootstrapExponent n := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hn1 : ((n : ℝ) + 1) + 1 ≠ 0 := by positivity
  rw [bootstrapExponent, bootstrapExponent]
  push_cast
  field_simp
  ring

theorem hasExponent_one_of_improvement (B : ℝ → ℝ → ℝ)
    (hTwo : HasExponent B 2)
    (hImprove : ∀ α : ℝ, 1 < α → α ≤ 2 → HasExponent B α →
      HasExponent B (2 - 1 / α)) :
    HasExponent B 1 := by
  have hInd : ∀ n : ℕ, HasExponent B (bootstrapExponent n) := by
    intro n
    induction n with
    | zero => simpa using hTwo
    | succ n ih =>
      rw [bootstrapExponent_succ]
      exact hImprove _ (bootstrapExponent_bounds n).1 (bootstrapExponent_bounds n).2 ih
  refine hasExponent_one_of_approximation B ?_
  intro η hη
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  refine ⟨bootstrapExponent n, ?_, hInd n⟩
  rw [bootstrapExponent]
  linarith

end DedekindZetaZeroFree.LargeSieve
