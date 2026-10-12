module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped Classical

theorem balancedRow_finiteFiber_mass_le
    {Row Index : Type*} (rows : Multiset Row) (indices : Finset Index)
    (index : Row → Index) (mass : Index → ℝ) (k₀ : ℕ)
    (hindex : ∀ x ∈ rows, index x ∈ indices)
    (hfiber : ∀ i ∈ indices, (rows.filter (fun x => index x = i)).card ≤ k₀)
    (hmass : ∀ i ∈ indices, 0 ≤ mass i) :
    (rows.map (fun x => mass (index x))).sum ≤ (k₀ : ℝ) * ∑ i ∈ indices, mass i := by
  classical
  let mapped := rows.map index
  have hmapped : ∀ i ∈ mapped, i ∈ indices := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hi
    exact hindex x hx
  have hsub : mapped.toFinset ⊆ indices := by
    intro i hi
    exact hmapped i (Multiset.mem_toFinset.mp hi)
  have hcount : ∀ i ∈ indices, mapped.count i ≤ k₀ := by
    intro i hi
    simpa [mapped, Multiset.count_map, eq_comm] using hfiber i hi
  calc
    (rows.map (fun x => mass (index x))).sum = (mapped.map mass).sum := by
      simp [mapped, Multiset.map_map, Function.comp_def]
    _ = ∑ i ∈ mapped.toFinset, mapped.count i • mass i :=
      Finset.sum_multiset_map_count mapped mass
    _ ≤ ∑ i ∈ mapped.toFinset, (k₀ : ℝ) * mass i := by
      apply Finset.sum_le_sum
      intro i hi
      have him := hsub hi
      simpa only [nsmul_eq_mul] using
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcount i him)) (hmass i him)
    _ ≤ ∑ i ∈ indices, (k₀ : ℝ) * mass i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro i hi _
      exact mul_nonneg (Nat.cast_nonneg _) (hmass i hi)
    _ = (k₀ : ℝ) * ∑ i ∈ indices, mass i := by rw [Finset.mul_sum]

theorem balancedRow_finiteFiber_norm_sq_le
    {Row Index : Type*} (rows : Multiset Row) (indices : Finset Index)
    (index : Row → Index) (B : Row → ℂ) (canonicalB : Index → ℂ) (k₀ : ℕ)
    (hindex : ∀ x ∈ rows, index x ∈ indices)
    (hfiber : ∀ i ∈ indices, (rows.filter (fun x => index x = i)).card ≤ k₀)
    (hdescend : ∀ x ∈ rows, B x = canonicalB (index x)) :
    (rows.map (fun x => ‖B x‖ ^ 2)).sum ≤
      (k₀ : ℝ) * ∑ i ∈ indices, ‖canonicalB i‖ ^ 2 := by
  have heq : rows.map (fun x => ‖B x‖ ^ 2) =
      rows.map (fun x => ‖canonicalB (index x)‖ ^ 2) := by
    apply Multiset.map_congr rfl
    intro x hx
    rw [hdescend x hx]
  rw [heq]
  exact balancedRow_finiteFiber_mass_le rows indices index
    (fun i => ‖canonicalB i‖ ^ 2) k₀ hindex hfiber (fun i _ => sq_nonneg _)

end
end DedekindZetaZeroFree
