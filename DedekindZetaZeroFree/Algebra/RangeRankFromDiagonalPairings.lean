module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.TameWhittakerSteps.Uniqueness.ReverseMinor

noncomputable section
set_option autoImplicit false

theorem rank_map_range_ge_two_of_diagonal_pairings
    {K V W X : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup X] [Module K X]
    (f : V →ₗ[K] W) (g : W →ₗ[K] X) (v₀ v₁ : V) (ell₀ ell₁ : Module.Dual K X)
    (c₀ c₁ : K) (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    (h₀₀ : ell₀ (g (f v₀)) = c₀) (h₀₁ : ell₀ (g (f v₁)) = 0)
    (h₁₀ : ell₁ (g (f v₀)) = 0) (h₁₁ : ell₁ (g (f v₁)) = c₁) :
    (2 : Cardinal) ≤ Module.rank K ((LinearMap.range f).map g) := by
  have hli : LinearIndependent K ![g (f v₀), g (f v₁)] := by
    rw [linearIndependent_fin2]
    refine ⟨?_, ?_⟩
    · intro h
      have hz : g (f v₁) = 0 := by simpa using h
      exact hc₁ (by rw [← h₁₁, hz, map_zero])
    · intro a h
      have h' : a • g (f v₁) = g (f v₀) := by simpa using h
      have h1 : ell₀ (a • g (f v₁)) = ell₀ (g (f v₀)) := by rw [h']
      simp only [map_smul, h₀₁, h₀₀, smul_zero] at h1
      exact hc₀ h1.symm
  haveI : Module.Finite K (Submodule.span K (Set.range ![g (f v₀), g (f v₁)])) :=
    Module.Finite.span_of_finite K (Set.finite_range _)
  have hrank : Module.rank K (Submodule.span K (Set.range ![g (f v₀), g (f v₁)])) =
      (2 : Cardinal) := by
    rw [← Module.finrank_eq_rank, finrank_span_eq_card hli]
    simp
  have hle : Submodule.span K (Set.range ![g (f v₀), g (f v₁)]) ≤
      (LinearMap.range f).map g := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.mem_map_of_mem (LinearMap.mem_range_self f v₀)
    · exact Submodule.mem_map_of_mem (LinearMap.mem_range_self f v₁)
  exact le_trans (le_of_eq hrank.symm) (Submodule.rank_mono hle)

end

end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.TameWhittakerSteps.Uniqueness.ReverseMinor
