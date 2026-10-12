module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.EmbedsInRayClassField

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Conductors of finite abelian extensions
-/

namespace ClassFieldTheory

universe u v

/-- A modulus is the conductor of a finite abelian extension when it is
exactly the least modulus whose ray class field contains the extension. -/
def IsAbelianConductor
    (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L]
    (c : RayClassModulus K) : Prop :=
  ∀ m : RayClassModulus K,
    EmbedsInRayClassField K L m ↔ c ≤ m

end ClassFieldTheory
