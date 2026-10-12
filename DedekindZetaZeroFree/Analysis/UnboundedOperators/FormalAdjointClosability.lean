module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

@[expose] public section

namespace DedekindZetaZeroFree

theorem formalAdjoint_gradient_closable
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V) (δ : V →ₗ.[ℂ] H)
    (hδ : Dense (δ.domain : Set V)) (hformal : D.IsFormalAdjoint δ) :
    D ≤ δ.adjoint ∧ D.IsClosable ∧ D.closure.IsClosed := by
  have hle : D ≤ δ.adjoint := hformal.symm.le_adjoint hδ
  have hcl : D.IsClosable := (LinearPMap.adjoint_isClosed hδ).isClosable.leIsClosable hle
  exact ⟨hle, hcl, hcl.closure_isClosed⟩

end DedekindZetaZeroFree
