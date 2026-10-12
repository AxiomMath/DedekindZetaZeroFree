module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.ClassGroup.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Fractional-ideal group of a number field
-/

open scoped NumberField
open NumberField

namespace ClassFieldTheory

universe u

/-- The group of nonzero fractional ideals of a number field. -/
abbrev NumberFieldFractionalIdealGroup
    (K : Type u) [Field K] [NumberField K] :=
  (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ

end ClassFieldTheory
