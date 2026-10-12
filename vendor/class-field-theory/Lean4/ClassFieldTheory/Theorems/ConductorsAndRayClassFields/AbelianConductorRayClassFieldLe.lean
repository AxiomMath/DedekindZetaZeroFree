module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The conductor of a ray class field

The conductor of the ray class field for a modulus `m` is bounded above by
`m`. Equality need not hold: a modulus may contain redundant conditions.
-/

namespace ClassFieldTheory

universe u

/-- A ray class field's conductor is at most its defining modulus. -/
theorem IsAbelianConductor.le_rayClassFieldModulus
    {K : Type u} [Field K] [NumberField K]
    {m c : RayClassModulus K}
    (R : RayClassFieldRealization K m)
    (hc : IsAbelianConductor K R.extension c) :
    c ≤ m := by
  apply (hc m).mp
  exact ⟨R, ⟨AlgHom.id K R.extension⟩⟩

end ClassFieldTheory
