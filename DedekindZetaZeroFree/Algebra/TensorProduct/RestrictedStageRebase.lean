module

public import DedekindZetaZeroFree.Algebra.TensorProduct.RestrictedTensorSimplicity

@[expose] public section

namespace DedekindZetaZeroFree
namespace RestrictedTensorSimple

open scoped TensorProduct Classical

universe u v

variable {J : Type u} (V : J → Type v)
  [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]

noncomputable def rebaseMap (e : ∀ j, V j) (E B : Finset J) (hEB : E ⊆ B) :
    Core V e B →ₗ[ℂ] Core V e E :=
  Module.DirectLimit.lift ℂ (Level B) (fun s : Level B => Stage V s.1)
    (transition V e B)
    (fun s => stageInclusion V e E ⟨s.1, hEB.trans s.property⟩)
    (fun s t hst x => LinearMap.congr_fun
      (inclusion_insert V e E
        ⟨s.1, hEB.trans s.property⟩ ⟨t.1, hEB.trans t.property⟩ hst) x)

@[simp] theorem rebaseMap_stageInclusion (e : ∀ j, V j)
    (E B : Finset J) (hEB : E ⊆ B) (s : Level B) (z : Stage V s.1) :
    rebaseMap V e E B hEB (stageInclusion V e B s z) =
      stageInclusion V e E ⟨s.1, hEB.trans s.property⟩ z := by
  simp only [rebaseMap, stageInclusion, Module.DirectLimit.lift_of]

theorem rebaseMap_bijective (e : ∀ j, V j) (E B : Finset J) (hEB : E ⊆ B)
    (he : ∀ j ∉ E, e j ≠ 0) :
    Function.Bijective (rebaseMap V e E B hEB) := by
  classical
  letI : Nonempty (Level E) := ⟨⟨E, le_rfl⟩⟩
  letI : Nonempty (Level B) := ⟨⟨B, le_rfl⟩⟩
  constructor
  · intro x y hxy
    obtain ⟨s, z, hz⟩ := Module.DirectLimit.exists_of (x - y)
    change stageInclusion V e B s z = x - y at hz
    have hz0 : z = 0 := by
      apply stageInclusion_injective V e E he ⟨s.1, hEB.trans s.property⟩
      rw [map_zero, ← rebaseMap_stageInclusion V e E B hEB s z,
        hz, map_sub, hxy, sub_self]
    apply sub_eq_zero.mp
    rw [← hz, hz0, map_zero]
  · intro x
    obtain ⟨s, z, hz⟩ := Module.DirectLimit.exists_of x
    change stageInclusion V e E s z = x at hz
    let t : Level B := ⟨s.1 ∪ B, Finset.subset_union_right⟩
    refine ⟨stageInclusion V e B t
      (insert V e s.1 t.1 Finset.subset_union_left z), ?_⟩
    rw [rebaseMap_stageInclusion]
    exact (LinearMap.congr_fun
      (inclusion_insert V e E s ⟨t.1, hEB.trans t.property⟩
        Finset.subset_union_left) z).trans hz

noncomputable def rebaseEquiv (e : ∀ j, V j) (E B : Finset J) (hEB : E ⊆ B)
    (he : ∀ j ∉ E, e j ≠ 0) : Core V e B ≃ₗ[ℂ] Core V e E :=
  LinearEquiv.ofBijective (rebaseMap V e E B hEB)
    (rebaseMap_bijective V e E B hEB he)

@[simp] theorem rebaseEquiv_stageInclusion (e : ∀ j, V j)
    (E B : Finset J) (hEB : E ⊆ B) (he : ∀ j ∉ E, e j ≠ 0)
    (s : Level B) (z : Stage V s.1) :
    rebaseEquiv V e E B hEB he (stageInclusion V e B s z) =
      stageInclusion V e E ⟨s.1, hEB.trans s.property⟩ z :=
  rebaseMap_stageInclusion V e E B hEB s z

end RestrictedTensorSimple
end DedekindZetaZeroFree
