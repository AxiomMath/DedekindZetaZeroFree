module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Vendor

theorem finiteDescent (b : ℝ → ℝ) (N : ℝ) (r : ℕ) (L A R C0 : ℝ)
    (hN : 1 ≤ N) (hr : 1 ≤ r) (hL : 1 ≤ L) (hA : 1 ≤ A)
    (hR : 0 ≤ R) (hC0 : 0 ≤ C0)
    (hnonneg : ∀ n : ℝ, 1 ≤ n → n ≤ N → 0 ≤ b n)
    (hsmall : ∀ n : ℝ, 1 ≤ n → n ≤ Real.rpow N (1 / (r : ℝ)) →
      b n ≤ C0 * R * Real.rpow N (1 / (r : ℝ)))
    (hstep : ∀ n : ℝ, Real.rpow N (1 / (r : ℝ)) < n → n ≤ N →
      ∃ n' : ℝ, 1 ≤ n' ∧ n' ≤ n / Real.rpow N (1 / (r : ℝ)) ∧
        b n ≤ L * b n' + L * A * Real.rpow (Real.rpow N (1 / (r : ℝ))) 5 * R) :
    b N ≤ L ^ r * (C0 + (r : ℝ) * A) *
      Real.rpow (Real.rpow N (1 / (r : ℝ))) 5 * R := by
  let H : ℝ := Real.rpow N (1 / (r : ℝ))
  let D : ℝ := Real.rpow H 5 * R
  have hN0 : 0 ≤ N := le_trans (by norm_num) hN
  have hr0 : r ≠ 0 := by omega
  have hH : 1 ≤ H := Real.one_le_rpow hN (by positivity)
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hHr : H ^ r = N := by
    simpa [H, one_div] using Real.rpow_inv_natCast_pow hN0 hr0
  have hH5 : H ≤ Real.rpow H 5 := by
    change H ≤ H ^ (5 : ℝ)
    rw [Real.rpow_ofNat]
    exact le_self_pow₀ hH (by norm_num)
  have hD : 0 ≤ D := mul_nonneg (Real.rpow_nonneg (le_of_lt hH0) _) hR
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hbase : ∀ n : ℝ, 1 ≤ n → n ≤ H → b n ≤ C0 * D := by
    intro n hn hnH
    exact (hsmall n hn hnH).trans (by
      change C0 * R * H ≤ C0 * (Real.rpow H 5 * R)
      calc
        C0 * R * H ≤ C0 * R * Real.rpow H 5 :=
          mul_le_mul_of_nonneg_left hH5 (mul_nonneg hC0 hR)
        _ = C0 * (Real.rpow H 5 * R) := by ring)
  have hbound : ∀ k : ℕ, ∀ n : ℝ, 1 ≤ n → n ≤ N → n ≤ H ^ k →
      b n ≤ L ^ k * (C0 + (k : ℝ) * A) * D := by
    intro k
    induction k with
    | zero =>
        intro n hn hnN hnk
        simpa using hbase n hn (le_trans (by simpa using hnk) hH)
    | succ k ih =>
        intro n hn hnN hnk
        have hcoef : 0 ≤ C0 + (k : ℝ) * A := by positivity
        have hcoef' : C0 ≤ C0 + ((k + 1 : ℕ) : ℝ) * A :=
          le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hA0)
        have hpow : 1 ≤ L ^ (k + 1) := one_le_pow₀ hL
        by_cases hnH : n ≤ H
        · apply (hbase n hn hnH).trans
          apply mul_le_mul_of_nonneg_right _ hD
          exact hcoef'.trans (le_mul_of_one_le_left (le_trans hC0 hcoef') hpow)
        · obtain ⟨n', hn', hn'div, hrec⟩ := hstep n (lt_of_not_ge hnH) hnN
          have hn'N : n' ≤ N := by
            have : n / H ≤ n := div_le_self (by linarith) hH
            exact hn'div.trans (this.trans hnN)
          have hn'pow : n' ≤ H ^ k := by
            apply hn'div.trans
            apply (div_le_iff₀ hH0).2
            simpa [pow_succ, mul_comm] using hnk
          have hib := ih n' hn' hn'N hn'pow
          have hrec' : b n ≤ L * b n' + L * A * D := by
            simpa [H, D, mul_assoc] using hrec
          have hLP : L ≤ L ^ (k + 1) := by
            rw [pow_succ]
            nlinarith [one_le_pow₀ hL (n := k)]
          have hbonus : L * A * D ≤ L ^ (k + 1) * A * D :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLP hA0) hD
          calc
            b n ≤ L * (L ^ k * (C0 + (k : ℝ) * A) * D) + L * A * D :=
              hrec'.trans (add_le_add (mul_le_mul_of_nonneg_left hib hL0) le_rfl)
            _ ≤ L * (L ^ k * (C0 + (k : ℝ) * A) * D) + L ^ (k + 1) * A * D :=
              add_le_add le_rfl hbonus
            _ = L ^ (k + 1) * (C0 + ((k + 1 : ℕ) : ℝ) * A) * D := by
              rw [pow_succ, Nat.cast_add, Nat.cast_one]
              ring
  simpa [D, H, mul_assoc] using hbound r N hN le_rfl hHr.ge

end DedekindZetaZeroFree.LargeSieve.Vendor
