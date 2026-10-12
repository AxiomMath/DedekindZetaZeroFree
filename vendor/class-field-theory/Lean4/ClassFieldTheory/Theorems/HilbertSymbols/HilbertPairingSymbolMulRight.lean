module

public import ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingSymbol

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Hilbert-pairing symbol multiplication in the second argument

The symbol is multiplicative in its second representative.
-/

namespace ClassFieldTheory.HilbertPairing

universe u

/-- The symbol is multiplicative in its second representative. -/
@[simp]
theorem symbol_mul_right
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) (a b c : Kˣ) :
    B.symbol a (b * c) = B.symbol a b * B.symbol a c := by
  simp only [symbol, map_mul]

end ClassFieldTheory.HilbertPairing
