module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

theorem mellinStrongPairContinuation (P : WeakFEPair ℂ) (hk : P.k = 1)
    (hP : IsStrongFEPair P) :
    Differentiable ℂ P.Λ ∧
    Differentiable ℂ P.symm.Λ ∧
    (∀ s : ℂ, HasMellin P.f s (P.Λ s)) ∧
    (∀ s : ℂ, HasMellin P.g s (P.symm.Λ s)) ∧
    (∀ s : ℂ, P.Λ s = P.ε * P.symm.Λ (1 - s)) := by
  refine ⟨hP.differentiable_Λ, hP.symm.differentiable_Λ, hP.hasMellin,
    hP.symm.hasMellin, ?_⟩
  intro s
  have h := P.functional_equation (1 - s)
  rw [hk, Complex.ofReal_one, sub_sub_cancel, smul_eq_mul] at h
  exact h

end DedekindZetaZeroFree.Hecke
