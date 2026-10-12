module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Vendor

open scoped NumberField Classical

theorem finite_partition_quadratic_bound
    {α β ι κ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq ι] [DecidableEq κ]
    (R : Finset α) (C : Finset β) (P : Finset ι) (Q : Finset κ)
    (row : ι → Finset α) (col : κ → Finset β)
    (hR : R = P.biUnion row) (hC : C = Q.biUnion col)
    (hrow : Set.PairwiseDisjoint (↑P : Set ι) row)
    (hcol : Set.PairwiseDisjoint (↑Q : Set κ) col)
    (K : β → α → ℂ) (lam : β → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hblock : ∀ i ∈ P, ∀ j ∈ Q,
      ∑ a ∈ row i, ‖∑ b ∈ col j, lam b * K b a‖ ^ 2 ≤
        B * (∑ b ∈ col j, ‖lam b‖ ^ 2)) :
    ∑ a ∈ R, ‖∑ b ∈ C, lam b * K b a‖ ^ 2 ≤
      (P.card : ℝ) * (Q.card : ℝ) * B * (∑ b ∈ C, ‖lam b‖ ^ 2) := by
  classical

  have hcolsum : ∀ a, (∑ b ∈ C, lam b * K b a) = ∑ j ∈ Q, ∑ b ∈ col j, lam b * K b a := by
    intro a
    rw [hC, Finset.sum_biUnion hcol]

  have hpoint : ∀ a ∈ R, ‖∑ b ∈ C, lam b * K b a‖ ^ 2 ≤
      (Q.card : ℝ) * ∑ j ∈ Q, ‖∑ b ∈ col j, lam b * K b a‖ ^ 2 := by
    intro a _
    rw [hcolsum a]
    calc ‖∑ j ∈ Q, ∑ b ∈ col j, lam b * K b a‖ ^ 2
        ≤ (∑ j ∈ Q, ‖∑ b ∈ col j, lam b * K b a‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le Q _) 2
      _ ≤ (Q.card : ℝ) * ∑ j ∈ Q, ‖∑ b ∈ col j, lam b * K b a‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq

  have hfactor : (∑ i ∈ P, ∑ a ∈ row i,
        (Q.card : ℝ) * ∑ j ∈ Q, ‖∑ b ∈ col j, lam b * K b a‖ ^ 2)
      = (Q.card : ℝ) * ∑ i ∈ P, ∑ a ∈ row i,
          ∑ j ∈ Q, ‖∑ b ∈ col j, lam b * K b a‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]

  have hcollapse : (∑ i ∈ P, ∑ j ∈ Q, B * (∑ b ∈ col j, ‖lam b‖ ^ 2))
      = (P.card : ℝ) * (B * ∑ b ∈ C, ‖lam b‖ ^ 2) := by
    have hY : (∑ j ∈ Q, ∑ b ∈ col j, ‖lam b‖ ^ 2) = ∑ b ∈ C, ‖lam b‖ ^ 2 := by
      rw [hC]
      exact (Finset.sum_biUnion hcol).symm
    calc ∑ i ∈ P, ∑ j ∈ Q, B * (∑ b ∈ col j, ‖lam b‖ ^ 2)
        = ∑ i ∈ P, B * (∑ j ∈ Q, ∑ b ∈ col j, ‖lam b‖ ^ 2) :=
          Finset.sum_congr rfl fun i _ =>
            (Finset.mul_sum Q (fun j => ∑ b ∈ col j, ‖lam b‖ ^ 2) B).symm
      _ = (P.card : ℝ) * (B * (∑ j ∈ Q, ∑ b ∈ col j, ‖lam b‖ ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (P.card : ℝ) * (B * ∑ b ∈ C, ‖lam b‖ ^ 2) := by rw [hY]
  calc ∑ a ∈ R, ‖∑ b ∈ C, lam b * K b a‖ ^ 2
      = ∑ i ∈ P, ∑ a ∈ row i, ‖∑ b ∈ C, lam b * K b a‖ ^ 2 := by
        rw [hR, Finset.sum_biUnion hrow]
    _ ≤ ∑ i ∈ P, ∑ a ∈ row i,
          (Q.card : ℝ) * ∑ j ∈ Q, ‖∑ b ∈ col j, lam b * K b a‖ ^ 2 := by
        refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun a ha => ?_
        exact hpoint a (by rw [hR]; exact Finset.mem_biUnion.mpr ⟨i, hi, ha⟩)
    _ = (Q.card : ℝ) * ∑ i ∈ P, ∑ a ∈ row i,
          ∑ j ∈ Q, ‖∑ b ∈ col j, lam b * K b a‖ ^ 2 := hfactor
    _ = (Q.card : ℝ) * ∑ i ∈ P, ∑ j ∈ Q, ∑ a ∈ row i,
          ‖∑ b ∈ col j, lam b * K b a‖ ^ 2 := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ ≤ (Q.card : ℝ) * ∑ i ∈ P, ∑ j ∈ Q, B * (∑ b ∈ col j, ‖lam b‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hblock i hi j hj
    _ = (Q.card : ℝ) * ((P.card : ℝ) * (B * ∑ b ∈ C, ‖lam b‖ ^ 2)) := by
        rw [hcollapse]
    _ = (P.card : ℝ) * (Q.card : ℝ) * B * (∑ b ∈ C, ‖lam b‖ ^ 2) := by ring

end DedekindZetaZeroFree.LargeSieve.Vendor
