module

public import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The quotient induced by a finite Artin map

This is the specific isomorphism induced by the Artin map in
`FiniteAbelianReciprocityData`, not an arbitrarily chosen isomorphism.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The first-isomorphism-theorem map induced by a finite Artin map. -/
def finiteAbelianReciprocityQuotientEquiv
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L) :
    (RayClassGroup D.modulus ⧸ D.artin.ker) ≃* (L ≃ₐ[K] L) :=
  QuotientGroup.quotientKerEquivOfSurjective D.artin D.artin_surjective

end ClassFieldTheory

end
