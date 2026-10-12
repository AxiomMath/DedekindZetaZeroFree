module

public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
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
# Existence of the big Hilbert class field

The big Hilbert class field is characterized intrinsically as a finite
abelian extension unramified at every finite prime and containing every
other finite abelian extension with that property.  No particular field
chosen by the implementation appears in the statement.
-/

open scoped NumberField

namespace ClassFieldTheory

/-- A maximal finite-prime-unramified finite abelian extension exists. -/
theorem exists_bigHilbertClassField
    (K : Type) [Field K] [NumberField K] :
    ∃ E : FiniteAbelianExtension K, IsBigHilbertClassField E :=
  GlobalClassFieldComparison.exists_bigHilbertClassField K

end ClassFieldTheory
