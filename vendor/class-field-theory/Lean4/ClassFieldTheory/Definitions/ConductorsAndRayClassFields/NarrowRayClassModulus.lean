module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassModulus
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The narrow class-group modulus
-/

noncomputable section

open scoped Classical

namespace ClassFieldTheory

universe u

/-- The modulus with no finite exponent and positivity at every real place.
Its ray class group is the narrow ideal class group. -/
def narrowRayClassModulus
    (K : Type u) [Field K] [NumberField K] : RayClassModulus K where
  finitePart := 0
  infinitePart := Finset.univ

end ClassFieldTheory

end
