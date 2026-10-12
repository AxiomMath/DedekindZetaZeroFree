module

public import ClassFieldTheory.Definitions.HilbertSymbols.PowerClass

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Inversion of power classes

The quotient map to power classes preserves inverses.
-/

namespace ClassFieldTheory

universe u

/-- The class of an inverse is the inverse class. -/
@[simp]
theorem powerClass_inv
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) :
    powerClass K n a⁻¹ = (powerClass K n a)⁻¹ :=
  map_inv (powerClass K n) a

end ClassFieldTheory
