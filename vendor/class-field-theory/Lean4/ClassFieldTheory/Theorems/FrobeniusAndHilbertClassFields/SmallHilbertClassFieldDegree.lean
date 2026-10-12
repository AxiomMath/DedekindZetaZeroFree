module

public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Degree of the small Hilbert class field

Any extension satisfying the intrinsic small-Hilbert-class-field property
has degree equal to the ordinary class number of the base field.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- The small Hilbert class field has degree equal to the class number. -/
theorem smallHilbertClassField_degree_eq_classNumber
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E) :
    Module.finrank K E = NumberField.classNumber K :=
  GlobalClassFieldComparison.smallHilbertClassField_degree_eq_classNumber_of_isSmall K E hE

end ClassFieldTheory

end
