module

public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsUnramifiedAtFinitePlaces
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Unramifiedness at every place
-/

namespace ClassFieldTheory

universe u v

/-- A number-field extension is unramified at all finite and infinite places. -/
def IsEverywhereUnramified
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : Prop :=
  IsUnramifiedAtFinitePlaces K L ∧ IsUnramifiedAtInfinitePlaces K L

end ClassFieldTheory
