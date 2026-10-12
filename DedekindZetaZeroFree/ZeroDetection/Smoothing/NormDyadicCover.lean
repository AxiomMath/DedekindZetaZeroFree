module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section

def detector_sz_dyadicLower (U : ℝ) : ℕ :=
  ⌊Real.log (U ^ 2) / Real.log 2⌋₊

def detector_sz_dyadicUpper (U : ℝ) : ℕ :=
  ⌈Real.log (U ^ 11) / Real.log 2⌉₊

def detector_sz_dyadicIndices (U : ℝ) : Finset ℕ :=
  Finset.Ico (detector_sz_dyadicLower U) (detector_sz_dyadicUpper U)

private theorem dyadic_le_log (x : ℝ) (hx : 0 < x) (n : ℕ) :
    (2 : ℝ)^n ≤ x ↔ (n : ℝ) ≤ Real.log x / Real.log 2 := by
  rw [le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  rw [← Real.log_pow]
  exact (Real.log_le_log_iff (by positivity) hx).symm
private theorem dyadic_lt_log (x : ℝ) (hx : 0 < x) (n : ℕ) :
    (2 : ℝ)^n < x ↔ (n : ℝ) < Real.log x / Real.log 2 := by
  rw [lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  rw [← Real.log_pow]
  exact (Real.log_lt_log_iff (by positivity) hx).symm
private theorem dyadic_floor_band (x : ℝ) (hx : 1 ≤ x) :
    (2 : ℝ)^⌊Real.log x / Real.log 2⌋₊ ≤ x ∧
    x < (2 : ℝ)^(⌊Real.log x / Real.log 2⌋₊ + 1) := by
  have hpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  constructor
  · exact (dyadic_le_log x hpos _).2 (Nat.floor_le (div_nonneg (Real.log_nonneg hx) (Real.log_pos (by norm_num)).le))
  · apply lt_of_not_ge
    intro h
    have := (dyadic_le_log x hpos _).1 h
    have hh := Nat.lt_floor_add_one (Real.log x / Real.log 2)
    push_cast at this
    linarith
private theorem dyadic_ceil_band (x : ℝ) (hx : 1 < x) :
    (2 : ℝ)^(⌈Real.log x / Real.log 2⌉₊ - 1) < x ∧
    x ≤ (2 : ℝ)^⌈Real.log x / Real.log 2⌉₊ := by
  have hpos : 0 < x := lt_trans zero_lt_one hx
  have hr : 0 < Real.log x / Real.log 2 := div_pos (Real.log_pos hx) (Real.log_pos (by norm_num))
  have hn : ⌈Real.log x / Real.log 2⌉₊ ≠ 0 := by
    have := (Nat.one_le_ceil_iff).2 hr
    omega
  have hb := (Nat.ceil_eq_iff hn).1 (rfl : ⌈Real.log x / Real.log 2⌉₊ = ⌈Real.log x / Real.log 2⌉₊)
  constructor
  · exact (dyadic_lt_log x hpos _).2 hb.1
  · apply le_of_not_gt
    intro h
    have hh := (dyadic_lt_log x hpos _).1 h
    linarith [hb.2]

theorem detector_sz_dyadic_cover (U : ℝ) (hU : 2 ≤ U) :
    detector_sz_dyadicLower U < detector_sz_dyadicUpper U ∧
    (∀ j : ℕ, j ∈ detector_sz_dyadicIndices U ↔
      detector_sz_dyadicLower U ≤ j ∧ j < detector_sz_dyadicUpper U) ∧
    ((2 : ℝ) ^ detector_sz_dyadicLower U ≤ U ^ 2 ∧
      U ^ 2 < (2 : ℝ) ^ (detector_sz_dyadicLower U + 1)) ∧
    ((2 : ℝ) ^ (detector_sz_dyadicUpper U - 1) < U ^ 11 ∧
      U ^ 11 ≤ (2 : ℝ) ^ detector_sz_dyadicUpper U) ∧
    (∀ t : ℝ, U ^ 2 < t → t ≤ U ^ 11 →
      ∃! j : ℕ, j ∈ detector_sz_dyadicIndices U ∧
        (2 : ℝ) ^ j < t ∧ t ≤ (2 : ℝ) ^ (j + 1)) ∧
    (∀ j ∈ detector_sz_dyadicIndices U,
      U ^ 2 / 2 < (2 : ℝ) ^ j ∧ (2 : ℝ) ^ j ≤ U ^ 11) ∧
    ((detector_sz_dyadicIndices U).card : ℝ) ≤ 16 * (1 + Real.log U) := by
  have hU1 : 1 < U := by linarith
  have hUpos : 0 < U := by linarith
  have h2 : 1 ≤ U ^ 2 := one_le_pow₀ hU1.le
  have h11 : 1 < U ^ 11 := one_lt_pow₀ hU1 (by norm_num)
  have hwindow : U ^ 2 < U ^ 11 := pow_lt_pow_right₀ hU1 (by norm_num)
  have hlo := dyadic_floor_band (U ^ 2) h2
  have hhi := dyadic_ceil_band (U ^ 11) h11
  change (2 : ℝ)^detector_sz_dyadicLower U ≤ U^2 ∧ U^2 < (2 : ℝ)^(detector_sz_dyadicLower U + 1) at hlo
  change (2 : ℝ)^(detector_sz_dyadicUpper U - 1) < U^11 ∧ U^11 ≤ (2 : ℝ)^detector_sz_dyadicUpper U at hhi
  have hind : detector_sz_dyadicLower U < detector_sz_dyadicUpper U := by
    apply (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1
    exact lt_of_le_of_lt hlo.1 (lt_of_lt_of_le hwindow hhi.2)
  have hmem : ∀ j : ℕ, j ∈ detector_sz_dyadicIndices U ↔
      detector_sz_dyadicLower U ≤ j ∧ j < detector_sz_dyadicUpper U := by
    intro j
    simp [detector_sz_dyadicIndices]
  refine ⟨hind, hmem, hlo, hhi, ?_, ?_, ?_⟩
  · intro t htlo hthi
    have ht : 1 < t := lt_of_le_of_lt h2 htlo
    have hb := dyadic_ceil_band t ht
    let j := ⌈Real.log t / Real.log 2⌉₊ - 1
    have hc : 0 < ⌈Real.log t / Real.log 2⌉₊ := by
      apply Nat.pos_of_ne_zero
      intro hz
      have := (Nat.ceil_eq_zero).1 hz
      have : 0 < Real.log t / Real.log 2 := div_pos (Real.log_pos ht) (Real.log_pos (by norm_num))
      linarith
    have hj : j + 1 = ⌈Real.log t / Real.log 2⌉₊ := by dsimp [j]; omega
    have hb' : (2 : ℝ)^j < t ∧ t ≤ (2 : ℝ)^(j+1) := by simpa [j, hj] using hb
    have hjlo : detector_sz_dyadicLower U ≤ j := by
      have : detector_sz_dyadicLower U < j + 1 :=
        (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1
          (lt_of_le_of_lt hlo.1 (lt_of_lt_of_le htlo hb'.2))
      omega
    have hjhi : j < detector_sz_dyadicUpper U :=
      (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1
        (lt_of_lt_of_le hb'.1 (le_trans hthi hhi.2))
    refine ⟨j, ⟨(hmem j).2 ⟨hjlo, hjhi⟩, hb'⟩, ?_⟩
    intro k hk
    have hk1 : k < j + 1 :=
      (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 (lt_of_lt_of_le hk.2.1 hb'.2)
    have hj1 : j < k + 1 :=
      (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 (lt_of_lt_of_le hb'.1 hk.2.2)
    omega
  · intro j hj
    obtain ⟨hjlo, hjhi⟩ := (hmem j).1 hj
    constructor
    · have hp : (2 : ℝ)^detector_sz_dyadicLower U ≤ (2 : ℝ)^j :=
        pow_le_pow_right₀ (by norm_num) hjlo
      have hmul : U ^ 2 < (2 : ℝ)^detector_sz_dyadicLower U * 2 := by
        simpa only [pow_succ] using hlo.2
      linarith
    · have hjlast : j ≤ detector_sz_dyadicUpper U - 1 := by omega
      exact (pow_le_pow_right₀ (by norm_num) hjlast).trans hhi.1.le
  · have hlog : 0 ≤ Real.log U := Real.log_nonneg hU1.le
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hf := Nat.lt_floor_add_one (Real.log (U ^ 2) / Real.log 2)
    have hc := Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg h11.le) hlog2.le)
    change (detector_sz_dyadicUpper U : ℝ) < Real.log (U ^ 11) / Real.log 2 + 1 at hc
    change Real.log (U ^ 2) / Real.log 2 < (detector_sz_dyadicLower U : ℝ) + 1 at hf
    rw [Real.log_pow] at hf hc
    norm_num at hf hc
    have hlower : (3 / 5 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hm := mul_le_mul_of_nonneg_right hlower hlog
    have hr : 9 * Real.log U / Real.log 2 ≤ 15 * Real.log U := by
      apply (div_le_iff₀ hlog2).2
      nlinarith
    simp only [detector_sz_dyadicIndices, Nat.card_Ico, Nat.cast_sub hind.le]
    have he : 11 * Real.log U / Real.log 2 - 2 * Real.log U / Real.log 2 = 9 * Real.log U / Real.log 2 := by ring
    linarith

end
end DedekindZetaZeroFree
