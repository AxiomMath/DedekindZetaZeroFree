module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.EisensteinCubicCharacters

@[expose] public section

namespace DedekindZetaZeroFree.Eisenstein

private theorem sum_power_mul_one_sub_power (k : Type*) [Field k] [Fintype k]
    (a b : ℕ) (h : a + b < Fintype.card k - 1) :
    ∑ x : k, x ^ a * (1 - x) ^ b = 0 := by
  induction b generalizing a with
  | zero =>
      simpa using FiniteField.sum_pow_lt_card_sub_one k a (by simpa using h)
  | succ b ih =>
      calc
        ∑ x : k, x ^ a * (1 - x) ^ (b + 1) =
            (∑ x : k, x ^ a * (1 - x) ^ b) -
              (∑ x : k, x ^ (a + 1) * (1 - x) ^ b) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          simp only [pow_succ]
          ring
        _ = 0 := by
          rw [ih a (by omega), ih (a + 1) (by omega), sub_self]

theorem sum_cubic_power_eq_zero (k : Type*) [Field k] [Fintype k]
    (hQ : 3 ∣ Fintype.card k - 1) :
    let d := (Fintype.card k - 1) / 3
    ∑ x : k, x ^ d * (1 - x) ^ d = 0 := by
  have hcard : 1 < Fintype.card k := Fintype.one_lt_card
  have hmul := Nat.div_mul_cancel hQ
  dsimp
  apply sum_power_mul_one_sub_power
  omega

theorem redq_jacobiSum_ρq (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    letI := residueFintype E q hq0
    redq E q
      (jacobiSum (ρq E ω hω q hq0 hqp hq6) (ρq E ω hω q hq0 hqp hq6)) = 0 := by
  letI := residueFintype E q hq0
  letI := residueField E q hq0 hqp
  simp only [jacobiSum, map_sum, map_mul, redq_ρq E ω hω q hq0 hqp hq6]
  exact sum_cubic_power_eq_zero (R E ⧸ q)
    (three_dvd_residueCard_sub_one E q hq0 hqp hq6)

theorem jacobiSum_ρq_mem (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    letI := residueFintype E q hq0
    jacobiSum (ρq E ω hω q hq0 hqp hq6) (ρq E ω hω q hq0 hqp hq6) ∈ q := by
  letI := residueFintype E q hq0
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    (redq_jacobiSum_ρq E ω hω q hq0 hqp hq6)

end DedekindZetaZeroFree.Eisenstein
