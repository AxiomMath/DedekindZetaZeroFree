module

public import DedekindZetaZeroFree.CharacterSums.DavenportHasse.PrimePowerMultiplicationReindexing
public import DedekindZetaZeroFree.CharacterSums.DavenportHasse.PolynomialDivisorSums

@[expose] public section

open Polynomial

namespace DavenportHasse.PolyPart

open scoped Classical

variable {k : Type*} [Field k] [Fintype k]

theorem convolution (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (n : ℕ) :
    (n : ℂ) * a χ ψ n =
      ∑ m ∈ Finset.Icc 1 n, b χ ψ m * a χ ψ (n - m) := by
  symm
  rw [convolution_reindexed]
  trans ∑ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n, ∑ P ∈ Mon k d,
    ∑ f ∈ Mon k n, if Irreducible P ∧ P ^ j ∣ f then (d : ℂ) * wt χ ψ f else 0
  · refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun j hj => ?_
    by_cases h : d * j ≤ n
    · rw [if_pos h]
      refine Finset.sum_congr rfl fun P hP => ?_
      have hPm := (mem_Mon.1 hP).1
      have hPd := (mem_Mon.1 hP).2
      by_cases hirr : Irreducible P
      · rw [if_pos hirr, mul_assoc]
        have hr := mul_reindex χ ψ hPm j n (by simpa [hPd, Nat.mul_comm] using h)
        rw [hPd, Nat.mul_comm j d] at hr
        rw [hr, Finset.mul_sum]
        refine Finset.sum_congr rfl fun f hf => ?_
        by_cases hv : P ^ j ∣ f <;> simp [hirr, hv]
      · simp [hirr]
    · rw [if_neg h]
      symm
      refine Finset.sum_eq_zero fun P hP => Finset.sum_eq_zero fun f hf => ?_
      have hnot : ¬ P ^ j ∣ f := by
        intro hv
        have hnd := natDegree_le_of_dvd hv (mem_Mon.1 hf).1.ne_zero
        rw [natDegree_pow, (mem_Mon.1 hP).2, (mem_Mon.1 hf).2] at hnd
        exact h (by simpa [Nat.mul_comm] using hnd)
      simp [hnot]
  · calc
      _ = ∑ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n, ∑ f ∈ Mon k n,
          ∑ P ∈ Mon k d, if Irreducible P ∧ P ^ j ∣ f then (d : ℂ) * wt χ ψ f else 0 := by
        refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun j hj => ?_
        exact Finset.sum_comm
      _ = ∑ d ∈ Finset.Icc 1 n, ∑ f ∈ Mon k n, ∑ j ∈ Finset.Icc 1 n,
          ∑ P ∈ Mon k d, if Irreducible P ∧ P ^ j ∣ f then (d : ℂ) * wt χ ψ f else 0 := by
        refine Finset.sum_congr rfl fun d hd => ?_
        exact Finset.sum_comm
      _ = ∑ f ∈ Mon k n, ∑ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n,
          ∑ P ∈ Mon k d, if Irreducible P ∧ P ^ j ∣ f then (d : ℂ) * wt χ ψ f else 0 :=
        Finset.sum_comm
      _ = ∑ f ∈ Mon k n, (n : ℂ) * wt χ ψ f := by
        refine Finset.sum_congr rfl fun f hf => ?_
        have hc := core (mem_Mon.1 hf).1
        rw [(mem_Mon.1 hf).2] at hc
        have hcast : (∑ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n, ∑ P ∈ Mon k d,
            if Irreducible P ∧ P ^ j ∣ f then (d : ℂ) else 0) = (n : ℂ) := by
          exact_mod_cast hc
        rw [← hcast, Finset.sum_mul]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun P hP => ?_
        split_ifs <;> simp
      _ = (n : ℂ) * a χ ψ n := by
        simp only [a, sum_Mon, Finset.mul_sum]

end DavenportHasse.PolyPart
