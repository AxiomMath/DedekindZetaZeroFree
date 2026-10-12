module

public import Mathlib.Tactic

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

theorem power_mul_stretchedExp_le (a p : ℝ) (ha : 0 < a) (hp : 0 < p)
    (R : ℝ) (hR : 0 ≤ R) (t : ℝ) (ht : 1 ≤ t) :
    let L : ℝ := 2 + 2 * R / (a * p)
    Real.rpow t R * Real.exp (-a * Real.rpow t p) ≤
      Real.exp ((R / p) * Real.log L) * Real.exp (-(a / 2) * Real.rpow t p) := by
  dsimp only
  let L : ℝ := 2 + 2 * R / (a * p)
  let q : ℝ := R / p
  let y : ℝ := Real.rpow t p
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hy : 0 < y := Real.rpow_pos_of_pos htpos p
  have hq : 0 ≤ q := div_nonneg hR hp.le
  have hL : 0 < L := by
    dsimp [L]
    positivity
  have hidentity : (a / 2) * L = a + q := by
    dsimp [L, q]
    field_simp
    <;> ring
  have hqL : q / L ≤ a / 2 := by
    apply (div_le_iff₀ hL).2
    rw [hidentity]
    linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hy hL)
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hL)] at hlog
  have hlogq := mul_le_mul_of_nonneg_left hlog hq
  have hdecay := mul_le_mul_of_nonneg_right hqL hy.le
  have hexponent : q * Real.log y - (a / 2) * y ≤ q * Real.log L := by
    have heq : q * (y / L) = (q / L) * y := by ring
    rw [← heq] at hdecay
    nlinarith
  have hlogy : Real.log y = p * Real.log t := Real.log_rpow htpos p
  have hqlog : q * Real.log y = Real.log t * R := by
    rw [hlogy]
    dsimp [q]
    field_simp
  change Real.rpow t R * Real.exp (-a * y) ≤
    Real.exp (q * Real.log L) * Real.exp (-(a / 2) * y)
  have hpow : Real.rpow t R = Real.exp (Real.log t * R) :=
    Real.rpow_def_of_pos htpos R
  rw [hpow, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hqlog] at hexponent
  linarith

end DedekindZetaZeroFree.Hecke
