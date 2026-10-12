module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import DedekindZetaZeroFree.LargeSieve.Exponents.ExponentAndRecursiveEnvelope

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve

theorem crossover_large_scale_bound (α M N : ℝ) (hα : 1 ≤ α) (hα₂ : α ≤ 2)
    (hM : 1 ≤ M) (hN : 1 ≤ N) :
    let β : ℝ := 2 - 1 / α
    (1 ≤ β ∧ β ≤ 2) ∧ 1 ≤ N ^ β ∧ N ≤ N ^ β ∧
      N ^ β * N ≤ (M * N) ^ (3 : ℝ) := by
  have hα0 : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hdiv1 : 1 / α ≤ 1 := (div_le_one hα0).mpr hα
  have hdiv0 : 0 ≤ 1 / α := by positivity
  have hβ1 : 1 ≤ 2 - 1 / α := by linarith
  have hβ2 : 2 - 1 / α ≤ 2 := by linarith
  have hβ0 : 0 ≤ 2 - 1 / α := le_trans zero_le_one hβ1
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  refine ⟨⟨hβ1, hβ2⟩, Real.one_le_rpow hN hβ0, ?_, ?_⟩
  · calc N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ ≤ N ^ (2 - 1 / α) := Real.rpow_le_rpow_of_exponent_le hN hβ1
  · have h3 : N ^ (2 - 1 / α) ≤ N ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN hβ2
    have h4 : N ^ (2 - 1 / α) * N ≤ N ^ (2 : ℝ) * N :=
      mul_le_mul_of_nonneg_right h3 hN0
    have h5 : N ^ (2 : ℝ) * N = N ^ (3 : ℝ) := by
      nth_rewrite 2 [← Real.rpow_one N]
      rw [← Real.rpow_add hNpos]
      norm_num
    have h6 : N ^ (3 : ℝ) ≤ (M * N) ^ (3 : ℝ) := by
      refine Real.rpow_le_rpow hN0 ?_ (by norm_num)
      nlinarith [hM, hN0]
    calc N ^ (2 - 1 / α) * N ≤ N ^ (2 : ℝ) * N := h4
      _ = N ^ (3 : ℝ) := h5
      _ ≤ (M * N) ^ (3 : ℝ) := h6

end DedekindZetaZeroFree.LargeSieve
