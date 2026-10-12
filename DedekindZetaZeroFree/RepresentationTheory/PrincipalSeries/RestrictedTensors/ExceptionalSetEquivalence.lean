module

public import DedekindZetaZeroFree.Algebra.TensorProduct.RestrictedTensorSimplicity

@[expose] public section

noncomputable section
open scoped Classical TensorProduct
namespace DedekindZetaZeroFree.RestrictedTensorSimple
variable {J : Type} (V : J → Type) [∀j, AddCommGroup (V j)] [∀j, Module ℂ (V j)]
variable (e : ∀j, V j) (B D : Finset J) (h : B = D)
def equalBadEquiv : Core V e B ≃ₗ[ℂ] Core V e D := by
  subst D
  exact LinearEquiv.refl ℂ _

theorem equalBadEquiv_stage (s : Level B) (x : Stage V s.val) :
    equalBadEquiv V e B D h (stageInclusion V e B s x) =
      stageInclusion V e D ⟨s.val, h ▸ s.property⟩ x := by
  subst D
  rfl
end DedekindZetaZeroFree.RestrictedTensorSimple

end
