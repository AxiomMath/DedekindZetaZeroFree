module

public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPLiteralResidueDescent

theorem factor_through_surjection
    {𝕜 U V W : Type*} [Field 𝕜]
    [AddCommGroup U] [Module 𝕜 U]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W]
    (q : U →ₗ[𝕜] V) (hq : Function.Surjective q)
    (A : U →ₗ[𝕜] W) (hker : ∀ x, q x = 0 → A x = 0) :
    ∃ B : V →ₗ[𝕜] W, ∀ x, B (q x) = A x := by
  have hle : LinearMap.ker q ≤ LinearMap.ker A := fun x hx => hker x hx
  refine ⟨((LinearMap.ker q).liftQ A hle).comp
    (q.quotKerEquivOfSurjective hq).symm.toLinearMap, ?_⟩
  intro x
  simp [LinearMap.comp_apply, LinearMap.quotKerEquivOfSurjective_symm_apply q hq x]

end DedekindZetaZeroFree.KPLiteralResidueDescent

end
