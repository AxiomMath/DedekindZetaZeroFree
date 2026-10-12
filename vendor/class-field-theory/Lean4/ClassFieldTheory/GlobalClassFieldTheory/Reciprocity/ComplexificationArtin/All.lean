module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.InfinitePlaceCompatibility
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.InfinitePlaceOverfield
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.NumberFieldComplexification
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.OverextensionArtin
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.RamifiedOverextension
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.RationalComplexification

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-!
# Artin reciprocity for the cyclotomic complexification

This compatibility module reexports the semantic layers constructing the
rational fourth-root complexification, its compositum with a number field,
the complex-conjugation overextension at a ramified real place, and the
resulting infinite-place local-global Artin comparison.
-/
