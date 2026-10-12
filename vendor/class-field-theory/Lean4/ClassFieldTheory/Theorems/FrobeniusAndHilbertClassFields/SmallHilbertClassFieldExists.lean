module

public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Existence of the small Hilbert class field

The small Hilbert class field is characterized as an everywhere-unramified
finite abelian extension containing every other such extension.  In
particular, real places are required to remain unramified.
-/

open scoped NumberField

namespace ClassFieldTheory

/-- A maximal everywhere-unramified finite abelian extension exists. -/
theorem exists_smallHilbertClassField
    (K : Type) [Field K] [NumberField K] :
    ∃ E : FiniteAbelianExtension K, IsSmallHilbertClassField E :=
  GlobalClassFieldComparison.exists_smallHilbertClassField K

end ClassFieldTheory
