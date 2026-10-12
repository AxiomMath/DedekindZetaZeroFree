module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.FiniteCompactOrbits
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.HarmonicCoreFiniteness

@[expose] public section

noncomputable section
open scoped Classical TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource

variable {X : Type*}

def functionProduct (U V : Submodule ℂ (X → ℂ)) : Submodule ℂ (X → ℂ) :=
  LinearMap.range (TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun (f : U) (g : V) => f.val * g.val)
    (by intros; ext x; simp [add_mul])
    (by intros; ext x; simp [mul_assoc])
    (by intros; ext x; simp [mul_add])
    (by intros; ext x; simp [mul_left_comm])))

theorem functionProduct_finite (U V : Submodule ℂ (X → ℂ))
    [Module.Finite ℂ U] [Module.Finite ℂ V] : Module.Finite ℂ (functionProduct U V) := by
  unfold functionProduct
  infer_instance

theorem mul_mem_functionProduct (U V : Submodule ℂ (X → ℂ))
    {f g : X → ℂ} (hf : f ∈ U) (hg : g ∈ V) : f * g ∈ functionProduct U V := by
  exact ⟨(⟨f, hf⟩ : U) ⊗ₜ[ℂ] (⟨g, hg⟩ : V), rfl⟩

theorem finite_product_space {ι : Type*} (s : Finset ι)
    (U : ι → Submodule ℂ (X → ℂ)) (hU : ∀ i ∈ s, Module.Finite ℂ (U i)) :
    ∃ W : Submodule ℂ (X → ℂ), Module.Finite ℂ W ∧
      ∀ f : ι → (X → ℂ), (∀ i ∈ s, f i ∈ U i) → (∏ i ∈ s, f i) ∈ W := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Submodule.span ℂ {1}, Module.Finite.of_fg (Submodule.fg_span (Set.finite_singleton _)), ?_⟩
    intro f hf
    simpa using (Submodule.subset_span (by simp : (1 : X → ℂ) ∈ ({1} : Set (X → ℂ))))
  | @insert i s hi ih =>
    obtain ⟨V, hV, hv⟩ := ih (fun j hj => hU j (Finset.mem_insert_of_mem hj))
    letI := hV
    letI := hU i (Finset.mem_insert_self _ _)
    refine ⟨functionProduct (U i) V, functionProduct_finite _ _, ?_⟩
    intro f hf
    rw [Finset.prod_insert hi]
    exact mul_mem_functionProduct _ _ (hf i (Finset.mem_insert_self _ _))
      (hv f (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource

end
