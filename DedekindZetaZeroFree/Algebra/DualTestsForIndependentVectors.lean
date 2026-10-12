module

public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.TameWhittakerSteps.Uniqueness.ReverseMinor
noncomputable section
set_option autoImplicit false
open Module

theorem exists_dual_diagonal_pairings_of_independent
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    (x₁ x₂ : X) (h : LinearIndependent K ![x₁, x₂]) (c₁ c₂ : K) :
    ∃ (ell₁ ell₂ : Module.Dual K X),
      ell₁ x₁ = c₁ ∧ ell₁ x₂ = 0 ∧ ell₂ x₁ = 0 ∧ ell₂ x₂ = c₂ := by
  classical

  have hli : LinearIndepOn K id (![x₁, x₂] '' (Set.univ : Set (Fin 2))) :=
    LinearIndepOn.id_image (h.linearIndepOn (Set.univ : Set (Fin 2)))
  let t : Set X := hli.extend (Set.subset_univ _)
  let b : Basis t K X := .mk (hli.linearIndepOn_extend (Set.subset_univ _)) <| by
    simpa using hli.span_extend_eq_span (Set.subset_univ _)
  have mem1 : x₁ ∈ t :=
    hli.subset_extend _ (Set.mem_image_of_mem ![x₁, x₂] (Set.mem_univ 0))
  have mem2 : x₂ ∈ t :=
    hli.subset_extend _ (Set.mem_image_of_mem ![x₁, x₂] (Set.mem_univ 1))
  have hb1 : b ⟨x₁, mem1⟩ = x₁ := by simp [b]
  have hb2 : b ⟨x₂, mem2⟩ = x₂ := by simp [b]
  have hne : x₁ ≠ x₂ := by
    have h' := h.injective.ne (by decide : (0 : Fin 2) ≠ 1)
    simpa using h'

  let f1 : t → K := fun i => if (i : X) = x₁ then c₁ else 0
  let f2 : t → K := fun i => if (i : X) = x₂ then c₂ else 0
  refine ⟨b.constr K f1, b.constr K f2, ?_, ?_, ?_, ?_⟩
  · rw [← hb1, Basis.constr_basis]; simp [f1]
  · rw [← hb2, Basis.constr_basis]; simp [f1, hne.symm]
  · rw [← hb1, Basis.constr_basis]; simp [f2, hne]
  · rw [← hb2, Basis.constr_basis]; simp [f2]

end
end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.TameWhittakerSteps.Uniqueness.ReverseMinor
