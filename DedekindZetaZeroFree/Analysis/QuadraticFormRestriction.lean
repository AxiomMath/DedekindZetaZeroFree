module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Vendor

open scoped Classical

theorem finite_subrange_mask_sum_mul {α β : Type*} [DecidableEq β]
    (S S' : Finset β) (hS : S' ⊆ S) (K : β → α → ℂ) (lam : β → ℂ) (a : α) :
    (∑ b ∈ S, (if b ∈ S' then lam b else 0) * K b a) =
      ∑ b ∈ S', lam b * K b a := by
  have hzero : ∀ b ∈ S, b ∉ S' → (if b ∈ S' then lam b else 0) * K b a = 0 := by
    intro b _ hb
    simp [hb]
  rw [← Finset.sum_subset hS hzero]
  exact Finset.sum_congr rfl fun b hb => by simp [hb]

theorem finite_subrange_mask_sum_norm_sq {β : Type*} [DecidableEq β]
    (S S' : Finset β) (hS : S' ⊆ S) (lam : β → ℂ) :
    (∑ b ∈ S, ‖(if b ∈ S' then lam b else 0 : ℂ)‖ ^ 2) =
      ∑ b ∈ S', ‖lam b‖ ^ 2 := by
  have hzero : ∀ b ∈ S, b ∉ S' → ‖(if b ∈ S' then lam b else 0 : ℂ)‖ ^ 2 = 0 := by
    intro b _ hb
    simp [hb]
  rw [← Finset.sum_subset hS hzero]
  exact Finset.sum_congr rfl fun b hb => by simp [hb]

theorem finite_subrange_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R R' : Finset α) (S S' : Finset β) (hR : R' ⊆ R) (hS : S' ⊆ S)
    (K : β → α → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ lam : β → ℂ,
      (∑ a ∈ R, ‖∑ b ∈ S, lam b * K b a‖ ^ 2) ≤
        B * ∑ b ∈ S, ‖lam b‖ ^ 2) :
    ∀ lam : β → ℂ,
      (∑ a ∈ R', ‖∑ b ∈ S', lam b * K b a‖ ^ 2) ≤
        B * ∑ b ∈ S', ‖lam b‖ ^ 2 := by
  intro lam
  set lam' : β → ℂ := fun b => if b ∈ S' then lam b else 0 with hlam'
  have hmul : ∀ a : α, (∑ b ∈ S, lam' b * K b a) = ∑ b ∈ S', lam b * K b a := by
    intro a
    simpa only [hlam'] using finite_subrange_mask_sum_mul S S' hS K lam a
  have hnorm : (∑ b ∈ S, ‖lam' b‖ ^ 2) = ∑ b ∈ S', ‖lam b‖ ^ 2 := by
    simpa only [hlam'] using finite_subrange_mask_sum_norm_sq S S' hS lam
  calc (∑ a ∈ R', ‖∑ b ∈ S', lam b * K b a‖ ^ 2)
      = ∑ a ∈ R', ‖∑ b ∈ S, lam' b * K b a‖ ^ 2 :=
        Finset.sum_congr rfl fun a _ => by rw [hmul a]
    _ ≤ ∑ a ∈ R, ‖∑ b ∈ S, lam' b * K b a‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hR
          (fun a _ _ => sq_nonneg ‖∑ b ∈ S, lam' b * K b a‖)
    _ ≤ B * ∑ b ∈ S, ‖lam' b‖ ^ 2 := hbound lam'
    _ = B * ∑ b ∈ S', ‖lam b‖ ^ 2 := by rw [hnorm]

end DedekindZetaZeroFree.LargeSieve.Vendor
