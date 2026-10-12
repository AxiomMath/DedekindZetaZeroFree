module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {c : Ideal (𝓞 F)} (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
variable {a : Ideal (𝓞 F)}

private lemma mem_zero_one_neg_one_of_cube_eq_self {z : ℂ} (h : z ^ 3 = z) :
    z ∈ ({0, 1, -1} : Set ℂ) := by
  have hfac : z * (z - 1) * (z + 1) = z ^ 3 - z := by ring
  have hzero : z * (z - 1) * (z + 1) = 0 := by rw [hfac, sub_eq_zero.mpr h]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases mul_eq_zero.mp hzero with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (add_eq_zero_iff_eq_neg.mp h))

theorem quadraticFamily_eq_zero_iff
    (ha : Squarefree a) (hac : a ⊔ c = ⊤) (n : Ideal (𝓞 F)) :
    (Q.χ a) n = 0 ↔ n = ⊥ ∨ n ⊔ Q.cond a ≠ ⊤ :=
  (Q.χ a).eq_zero_iff' n

theorem quadraticFamily_mem_zero_one_neg_one
    (ha : Squarefree a) (hac : a ⊔ c = ⊤) (n : Ideal (𝓞 F)) :
    (Q.χ a) n ∈ ({0, 1, -1} : Set ℂ) :=
  mem_zero_one_neg_one_of_cube_eq_self (Q.quadratic a n ha hac)

theorem quadraticFamily_eq_one_or_neg_one
    (ha : Squarefree a) (hac : a ⊔ c = ⊤) (n : Ideal (𝓞 F))
    (hn : n ≠ ⊥) (hncond : n ⊔ Q.cond a = ⊤) :
    (Q.χ a) n = 1 ∨ (Q.χ a) n = -1 := by
  have hne : (Q.χ a) n ≠ 0 := by
    intro h0
    rcases (quadraticFamily_eq_zero_iff Q ha hac n).mp h0 with h | h
    · exact hn h
    · exact h hncond
  have hmem := quadraticFamily_mem_zero_one_neg_one Q ha hac n
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · exact absurd h hne
  · exact Or.inl h
  · exact Or.inr h

theorem quadraticFamily_value_sq_eq_one
    (ha : Squarefree a) (hac : a ⊔ c = ⊤) (n : Ideal (𝓞 F))
    (hn : n ≠ ⊥) (hncond : n ⊔ Q.cond a = ⊤) :
    ((Q.χ a) n) ^ 2 = 1 := by
  rcases quadraticFamily_eq_one_or_neg_one Q ha hac n hn hncond with h | h <;>
    rw [h] <;> norm_num

theorem quadraticFamily_conj
    (ha : Squarefree a) (hac : a ⊔ c = ⊤) (n : Ideal (𝓞 F)) :
    (starRingEnd ℂ) ((Q.χ a) n) = (Q.χ a) n := by
  have hmem := quadraticFamily_mem_zero_one_neg_one Q ha hac n
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h <;> rw [h] <;> simp

theorem quadraticFamily_norm_le_one
    (ha : Squarefree a) (hac : a ⊔ c = ⊤) (n : Ideal (𝓞 F)) :
    ‖(Q.χ a) n‖ ≤ 1 := by
  have hmem := quadraticFamily_mem_zero_one_neg_one Q ha hac n
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h <;> rw [h] <;> norm_num

end DedekindZetaZeroFree.LargeSieve
