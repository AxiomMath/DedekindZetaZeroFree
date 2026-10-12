module

public import DedekindZetaZeroFree.CharacterSums.DavenportHasse.WeightedVonMangoldtConvolution

@[expose] public section

namespace DavenportHasse

variable {k : Type*} [Field k] [Fintype k]

private lemma b_one (χ : MulChar k ℂ) (ψ : AddChar k ℂ) : b χ ψ 1 = gaussSum χ ψ := by
  have h := PolyPart.convolution χ ψ 1
  rw [Finset.Icc_self, Finset.sum_singleton] at h
  rw [PolyPart.a_one, PolyPart.a_zero] at h
  simp at h
  exact h.symm

private lemma b_step (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (hψ : ∃ x : k, ψ x ≠ 1)
    {n : ℕ} (hn : 2 ≤ n) : b χ ψ n = -gaussSum χ ψ * b χ ψ (n - 1) := by
  have hsum : (∑ m ∈ Finset.Icc 1 n, b χ ψ m * a χ ψ (n - m))
      = b χ ψ (n - 1) * a χ ψ 1 + b χ ψ n * a χ ψ 0 := by
    have hIcc : Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hIcc2 : Finset.Icc 1 (n - 1) = insert (n - 1) (Finset.Icc 1 (n - 2)) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hzero : (∑ m ∈ Finset.Icc 1 (n - 2), b χ ψ m * a χ ψ (n - m)) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      rw [Finset.mem_Icc] at hm
      rw [PolyPart.a_eq_zero χ ψ hψ (show 2 ≤ n - m by omega), mul_zero]
    rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega),
      hIcc2, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), hzero]
    rw [show n - n = 0 by omega, show n - (n - 1) = 1 by omega]
    ring
  have h := PolyPart.convolution χ ψ n
  rw [PolyPart.a_eq_zero χ ψ hψ hn, mul_zero] at h
  rw [hsum, PolyPart.a_one, PolyPart.a_zero, mul_one] at h
  have key : b χ ψ (n - 1) * gaussSum χ ψ + b χ ψ n = 0 := h.symm
  rw [neg_mul, mul_comm (gaussSum χ ψ), eq_neg_iff_add_eq_zero, add_comm]
  exact key

theorem b_eq (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (hψ : ∃ x : k, ψ x ≠ 1) {m : ℕ} (hm : 0 < m) :
    b χ ψ m = -(-gaussSum χ ψ) ^ m := by
  have hb1 : b χ ψ 1 = gaussSum χ ψ := b_one χ ψ
  have hmain : ∀ n, 1 ≤ n → b χ ψ n = -(-gaussSum χ ψ) ^ n := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0; simpa using hb1
      · have hstep := b_step χ ψ hψ (n := k + 1) (by omega)
        rw [hstep, show k + 1 - 1 = k by omega, ih (by omega), pow_succ]
        ring
  exact hmain m hm

end DavenportHasse
