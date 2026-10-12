module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

@[expose] public section

namespace DedekindZetaZeroFree

theorem thetaPolynomialGaussianAbsorption (d : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ P : ℝ, 0 < P ∧ ∀ u : ℝ, 0 ≤ u →
      (1 + u) ^ d * Real.exp (-a * u ^ 2) ≤
        P * Real.exp (-(a / 2) * u ^ 2) := by
  have ha2 : 0 < a / 2 := by linarith

  have hlit : (fun x : ℝ => Real.exp (-(a / 2) * x ^ 2)) =o[Filter.atTop]
      (fun x : ℝ => x ^ (-(d : ℝ))) := by
    have h := rexp_neg_quadratic_isLittleO_rpow_atTop (a := -(a / 2)) (b := 0)
      (s := -(d : ℝ)) (by linarith)
    simpa using h
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp (-(a / 2) * x ^ 2) ≤ x ^ (-(d : ℝ)) := by
    filter_upwards [hlit.bound (c := 1) one_pos,
      Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul] at hx
    exact hx
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max ((1 + max N₀ 1) ^ d) (2 ^ d), ?_, ?_⟩
  · exact lt_of_lt_of_le (pow_pos (by norm_num) d) (le_max_right _ _)
  · intro u hu

    have hfu : (1 + u) ^ d * Real.exp (-(a / 2) * u ^ 2) ≤
        max ((1 + max N₀ 1) ^ d) (2 ^ d) := by
      rcases le_or_gt u (max N₀ 1) with hle | hlt
      · calc (1 + u) ^ d * Real.exp (-(a / 2) * u ^ 2)
            ≤ (1 + max N₀ 1) ^ d * 1 := by
              refine mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) d) ?_
                (Real.exp_pos _).le (by positivity)
              rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg u]
            _ = (1 + max N₀ 1) ^ d := by ring
            _ ≤ max ((1 + max N₀ 1) ^ d) (2 ^ d) := le_max_left _ _
      · have huN₀ : N₀ ≤ u := le_trans (le_max_left _ _) hlt.le
        have hu1 : 1 ≤ u := le_trans (le_max_right _ _) hlt.le
        have htail : Real.exp (-(a / 2) * u ^ 2) ≤ u ^ (-(d : ℝ)) := hN₀ u huN₀
        calc (1 + u) ^ d * Real.exp (-(a / 2) * u ^ 2)
            ≤ (2 * u) ^ d * u ^ (-(d : ℝ)) := by
              refine mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) d) htail
                (Real.exp_pos _).le (by positivity)
            _ = 2 ^ d * (u ^ d * u ^ (-(d : ℝ))) := by rw [mul_pow]; ring
            _ = 2 ^ d * 1 := by
              congr 1
              rw [← Real.rpow_natCast u d, ← Real.rpow_add (by linarith : (0 : ℝ) < u)]
              rw [show (d : ℝ) + -(d : ℝ) = 0 by ring, Real.rpow_zero]
            _ = 2 ^ d := by ring
            _ ≤ max ((1 + max N₀ 1) ^ d) (2 ^ d) := le_max_right _ _

    have hexp : Real.exp (-a * u ^ 2) =
        Real.exp (-(a / 2) * u ^ 2) * Real.exp (-(a / 2) * u ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (1 + u) ^ d * Real.exp (-a * u ^ 2)
        = (1 + u) ^ d * Real.exp (-(a / 2) * u ^ 2) *
            Real.exp (-(a / 2) * u ^ 2) := by rw [hexp]; ring
      _ ≤ max ((1 + max N₀ 1) ^ d) (2 ^ d) * Real.exp (-(a / 2) * u ^ 2) :=
          mul_le_mul_of_nonneg_right hfu (Real.exp_pos _).le

end DedekindZetaZeroFree
