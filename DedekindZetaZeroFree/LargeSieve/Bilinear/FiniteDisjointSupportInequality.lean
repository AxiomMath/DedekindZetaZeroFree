module

public import Mathlib

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CoprimeBilinearBound.lean.
-/

namespace DedekindZetaZeroFree.LargeSieve.Vendor.CoprimeBilinear

noncomputable section
open scoped Classical BigOperators

private lemma sum_powerset_neg_one_pow_card_C {P : Type*} [DecidableEq P] (A : Finset P) :
    (∑ D ∈ A.powerset, (-1 : ℂ) ^ D.card) = if A = ∅ then 1 else 0 := by
  have h : ((∑ D ∈ A.powerset, (-1 : ℤ) ^ D.card : ℤ) : ℂ) =
      ((if A = ∅ then 1 else 0 : ℤ) : ℂ) := by
    rw [Finset.sum_powerset_neg_one_pow_card]
  rw [Int.cast_sum] at h
  simpa using h

private lemma disjoint_indicator_expansion {P : Type*} [DecidableEq P]
    (ambient S T : Finset P) (hS : S ⊆ ambient) (hT : T ⊆ ambient) :
    (∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
        (if D ⊆ S ∧ D ⊆ T then 1 else 0)) = if Disjoint S T then 1 else 0 := by
  have hfilter : ambient.powerset.filter (fun D => D ⊆ S ∧ D ⊆ T) = (S ∩ T).powerset := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨_, hDS, hDT⟩ x hx
      exact Finset.mem_inter.mpr ⟨hDS hx, hDT hx⟩
    · intro hD
      exact ⟨fun x hx => hS (Finset.mem_inter.mp (hD hx)).1,
        fun x hx => (Finset.mem_inter.mp (hD hx)).1,
        fun x hx => (Finset.mem_inter.mp (hD hx)).2⟩
  have hsum : (∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
        (if D ⊆ S ∧ D ⊆ T then 1 else 0))
      = ∑ D ∈ ambient.powerset.filter (fun D => D ⊆ S ∧ D ⊆ T), (-1 : ℂ) ^ D.card := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro D _
    split_ifs <;> simp
  rw [hsum, hfilter, sum_powerset_neg_one_pow_card_C]
  by_cases h : S ∩ T = ∅
  · rw [if_pos h, if_pos (Finset.disjoint_iff_inter_eq_empty.mpr h)]
  · rw [if_neg h, if_neg (fun hd => h (Finset.disjoint_iff_inter_eq_empty.mp hd))]

private lemma masked_coefficient_energy {P L : Type*} [DecidableEq P] [Fintype L]
    (B : Finset P) (left : L → Finset P) (hl : ∀ j, left j ⊆ B) (a : L → ℂ) :
    (∑ D ∈ B.powerset, ∑ j, ‖(if D ⊆ left j then a j else 0 : ℂ)‖ ^ 2)
      = ∑ j, (2 : ℝ) ^ (left j).card * ‖a j‖ ^ 2 := by
  have hterm : ∀ (D : Finset P) (j : L),
      ‖(if D ⊆ left j then a j else 0 : ℂ)‖ ^ 2 = if D ⊆ left j then ‖a j‖ ^ 2 else 0 := by
    intro D j
    by_cases h : D ⊆ left j <;> simp [h]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hstep : (∑ D ∈ B.powerset, (if D ⊆ left j then ‖a j‖ ^ 2 else 0 : ℝ))
      = (∑ D ∈ B.powerset, (if D ⊆ left j then (1 : ℝ) else 0)) * ‖a j‖ ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro D _
    split_ifs <;> ring
  rw [hstep]
  have hfilt : B.powerset.filter (fun D => D ⊆ left j) = (left j).powerset := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨fun x hx => hl j (h hx), h⟩⟩
  rw [Finset.sum_boole, hfilt, Finset.card_powerset]
  push_cast
  ring

theorem disjoint_bilinear_expansion
    {P L T : Type*} [DecidableEq P] [Fintype L] [Fintype T]
    (ambient : Finset P) (s : L → Finset P) (t : T → Finset P)
    (hs : ∀ l, s l ⊆ ambient) (ht : ∀ k, t k ⊆ ambient)
    (z : L → ℂ) (v : T → ℂ) :
    (∑ l, ∑ k, if Disjoint (s l) (t k) then z l * star (v k) else 0) =
      ∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
        ((∑ l, if D ⊆ s l then z l else 0) *
          star (∑ k, if D ⊆ t k then v k else 0)) := by
  have hp (l : L) (k : T) :
      (if Disjoint (s l) (t k) then z l * star (v k) else 0) =
      ∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
        (if D ⊆ s l ∧ D ⊆ t k then z l * star (v k) else 0) := by
    calc
      (if Disjoint (s l) (t k) then z l * star (v k) else 0)
          = (if Disjoint (s l) (t k) then (1 : ℂ) else 0) * (z l * star (v k)) := by
            split_ifs <;> simp
      _ = (∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
            (if D ⊆ s l ∧ D ⊆ t k then 1 else 0)) * (z l * star (v k)) := by
            rw [disjoint_indicator_expansion ambient (s l) (t k) (hs l) (ht k)]
      _ = ∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
            (if D ⊆ s l ∧ D ⊆ t k then z l * star (v k) else 0) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro D _
            split_ifs <;> simp
  simp_rw [hp]
  calc
    _ = ∑ l, ∑ D ∈ ambient.powerset, ∑ k, (-1 : ℂ) ^ D.card *
        (if D ⊆ s l ∧ D ⊆ t k then z l * star (v k) else 0) := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = ∑ D ∈ ambient.powerset, ∑ l, ∑ k, (-1 : ℂ) ^ D.card *
        (if D ⊆ s l ∧ D ⊆ t k then z l * star (v k) else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _
      simp_rw [← Finset.mul_sum]
      congr 1
      have hstar : star (∑ k, if D ⊆ t k then v k else 0)
          = ∑ k, if D ⊆ t k then star (v k) else 0 := by
        rw [star_sum]
        apply Finset.sum_congr rfl
        intro k _
        split_ifs <;> simp
      rw [hstar, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro k _
      by_cases hl : D ⊆ s l <;> by_cases hk : D ⊆ t k <;> simp [hl, hk]

theorem coprime_bilinear_operator_bound
    {R L T P : Type*} [Fintype R] [Fintype L] [Fintype T]
    [Fintype P] [DecidableEq P]
    (s : L → Finset P) (t : T → Finset P)
    (A : R → L → ℂ) (B : R → T → ℂ)
    (UA UB : ℝ) (hUA : 0 ≤ UA) (hUB : 0 ≤ UB)
    (hA : ∀ x : L → ℂ,
      (∑ r, ‖∑ l, A r l * x l‖ ^ 2) ≤ UA * ∑ l, ‖x l‖ ^ 2)
    (hB : ∀ y : T → ℂ,
      (∑ r, ‖∑ k, B r k * y k‖ ^ 2) ≤ UB * ∑ k, ‖y k‖ ^ 2)
    (x : L → ℂ) (y : T → ℂ) :
    (∑ r, ‖∑ l, ∑ k, if Disjoint (s l) (t k) then
      (A r l * x l) * star (B r k * y k) else 0‖) ^ 2 ≤
      UA * UB * (∑ l, (2 : ℝ) ^ (s l).card * ‖x l‖ ^ 2) *
        (∑ k, (2 : ℝ) ^ (t k).card * ‖y k‖ ^ 2) := by
  let ambient : Finset P := (Finset.univ.biUnion s) ∪ (Finset.univ.biUnion t)
  have hs : ∀ l, s l ⊆ ambient := fun l =>
    le_trans (Finset.subset_biUnion_of_mem s (Finset.mem_univ l)) Finset.subset_union_left
  have ht : ∀ k, t k ⊆ ambient := fun k =>
    le_trans (Finset.subset_biUnion_of_mem t (Finset.mem_univ k)) Finset.subset_union_right
  let X (D : Finset P) (r : R) : ℂ := ∑ l, A r l * (if D ⊆ s l then x l else 0)
  let Y (D : Finset P) (r : R) : ℂ := ∑ k, B r k * (if D ⊆ t k then y k else 0)
  have heq (r : R) :
      (∑ l, ∑ k, if Disjoint (s l) (t k) then
        (A r l * x l) * star (B r k * y k) else 0) =
        ∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card * (X D r * star (Y D r)) := by
    rw [disjoint_bilinear_expansion ambient s t hs ht (fun l => A r l * x l)
      (fun k => B r k * y k)]
    simp only [X, Y, mul_ite, mul_zero]
  have hnorm :
      (∑ r, ‖∑ l, ∑ k, if Disjoint (s l) (t k) then
        (A r l * x l) * star (B r k * y k) else 0‖) ≤
        ∑ D ∈ ambient.powerset, ∑ r, ‖X D r‖ * ‖Y D r‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro r _
    rw [heq r]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro D _
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_star]
    exact le_rfl
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (ambient.powerset ×ˢ (Finset.univ : Finset R))
    (fun di => ‖X di.1 di.2‖) (fun di => ‖Y di.1 di.2‖)
  simp only [Finset.sum_product] at hCS
  have hX : (∑ D ∈ ambient.powerset, ∑ r, ‖X D r‖ ^ 2) ≤
      UA * ∑ l, (2 : ℝ) ^ (s l).card * ‖x l‖ ^ 2 := by
    calc
      _ ≤ ∑ D ∈ ambient.powerset, UA * ∑ l, ‖(if D ⊆ s l then x l else 0 : ℂ)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro D _
        exact hA (fun l => if D ⊆ s l then x l else 0)
      _ = _ := by rw [← Finset.mul_sum, masked_coefficient_energy ambient s hs x]
  have hY : (∑ D ∈ ambient.powerset, ∑ r, ‖Y D r‖ ^ 2) ≤
      UB * ∑ k, (2 : ℝ) ^ (t k).card * ‖y k‖ ^ 2 := by
    calc
      _ ≤ ∑ D ∈ ambient.powerset, UB * ∑ k, ‖(if D ⊆ t k then y k else 0 : ℂ)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro D _
        exact hB (fun k => if D ⊆ t k then y k else 0)
      _ = _ := by rw [← Finset.mul_sum, masked_coefficient_energy ambient t ht y]
  have hmain : UA * UB * (∑ l, (2 : ℝ) ^ (s l).card * ‖x l‖ ^ 2) *
        (∑ k, (2 : ℝ) ^ (t k).card * ‖y k‖ ^ 2)
      = (UA * ∑ l, (2 : ℝ) ^ (s l).card * ‖x l‖ ^ 2) *
        (UB * ∑ k, (2 : ℝ) ^ (t k).card * ‖y k‖ ^ 2) := by ring
  rw [hmain]
  refine (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hnorm 2).trans
    (hCS.trans (mul_le_mul hX hY ?_ ?_))
  · exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  · exact mul_nonneg hUA (Finset.sum_nonneg (fun _ _ => mul_nonneg (by norm_num) (sq_nonneg _)))

end
end DedekindZetaZeroFree.LargeSieve.Vendor.CoprimeBilinear
