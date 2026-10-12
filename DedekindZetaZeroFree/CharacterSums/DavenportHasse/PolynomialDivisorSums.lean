module

public import DedekindZetaZeroFree.CharacterSums.DavenportHasse.MonicPolynomialCounting

@[expose] public section

open Polynomial

namespace DavenportHasse.PolyPart

open scoped Classical

variable {k : Type*} [Field k] [Fintype k]

theorem convolution_reindexed (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n, b χ ψ m * a χ ψ (n - m)) =
      ∑ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n,
        if d * j ≤ n then
          (∑ P ∈ Mon k d,
            if Irreducible P then
              (d : ℂ) * wt χ ψ P ^ j * a χ ψ (n - d * j)
            else 0)
        else 0 := by
  calc
    _ = ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ m.divisors,
        ∑ P ∈ Mon k d, if Irreducible P then
          (d : ℂ) * wt χ ψ P ^ (m / d) * a χ ψ (n - d * (m / d))
        else 0 := by
      refine Finset.sum_congr rfl fun m hm => ?_
      unfold b
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.sum_mul, ← sum_Mon]
      have hdm : d * (m / d) = m := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      simp only [hdm, ite_mul, zero_mul]
    _ = _ := divisors_reindex n (fun d j =>
      ∑ P ∈ Mon k d, if Irreducible P then
        (d : ℂ) * wt χ ψ P ^ j * a χ ψ (n - d * j) else 0)

end DavenportHasse.PolyPart
