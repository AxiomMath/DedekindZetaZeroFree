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
# Multiplication of power classes

The quotient map to power classes preserves multiplication.
-/

namespace ClassFieldTheory

universe u

/-- The class of a product is the product of the classes. -/
@[simp]
theorem powerClass_mul
    (K : Type u) [Field K] (n : ℕ+) (a b : Kˣ) :
    powerClass K n (a * b) = powerClass K n a * powerClass K n b :=
  map_mul (powerClass K n) a b

end ClassFieldTheory
