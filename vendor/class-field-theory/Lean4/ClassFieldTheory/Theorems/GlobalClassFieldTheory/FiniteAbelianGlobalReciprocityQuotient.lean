module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityQuotientEquiv

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Quotient form of finite abelian global reciprocity

The kernel of a finite ray-class Artin map is exactly the relation that must
be divided out to obtain the Galois group.  The modulus and Frobenius
normalization are carried by `FiniteAbelianReciprocityData`.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u v

/-- A finite Artin map induces an isomorphism from its ray-class quotient to
the finite abelian Galois group. -/
theorem finiteAbelianGlobalReciprocity_quotient
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L) :
    Nonempty
      ((RayClassGroup D.modulus ⧸ D.artin.ker) ≃* (L ≃ₐ[K] L)) := by
  exact ⟨finiteAbelianReciprocityQuotientEquiv K L D⟩

end ClassFieldTheory

end
