module

public import Mathlib.FieldTheory.KummerExtension

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Canonical Kummer algebras
-/

namespace ClassFieldTheory

universe u

/-- The Kummer algebra `K[X] / (X^n - a)`.  It remains canonical when the
polynomial is reducible, so no root in a chosen closure is required. -/
abbrev KummerAlgebra
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) :=
  AdjoinRoot (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K))

end ClassFieldTheory
