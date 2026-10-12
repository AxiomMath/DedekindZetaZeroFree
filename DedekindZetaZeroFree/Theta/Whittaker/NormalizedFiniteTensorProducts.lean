module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree

open scoped Classical

universe u w t r

def localWhittakerSpace (N : Type r) [Group N]
    (V : Type w) [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (ρ : Representation ℂ N V) (ψ : N →* ℂ) : Submodule ℂ (V →L[ℂ] ℂ) where
  carrier := {ℓ | ∀ n x, ℓ (ρ n x) = ψ n * ℓ x}
  zero_mem' := by simp
  add_mem' := by
    intro ℓ m hℓ hm n x
    simp only [ContinuousLinearMap.add_apply, hℓ n x, hm n x, mul_add]
  smul_mem' := by
    intro c ℓ hℓ n x
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hℓ n x]
    ring

end DedekindZetaZeroFree
