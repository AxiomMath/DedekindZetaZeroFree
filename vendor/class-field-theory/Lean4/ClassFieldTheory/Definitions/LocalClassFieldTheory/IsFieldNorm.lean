module

public import ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Predicate for field norms
-/

noncomputable section

namespace ClassFieldTheory

universe u v

/-- A nonzero element of `K` is a field norm from `L`. -/
def IsFieldNorm
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (x : Kˣ) : Prop :=
  x ∈ fieldNormSubgroup K L

end ClassFieldTheory

end
