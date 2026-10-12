module

public import ClassFieldTheory.Algebra.All
public import ClassFieldTheory.AbstractClassFieldTheory.All
public import ClassFieldTheory.AlgebraicNumberTheory.All
public import ClassFieldTheory.Definitions.All
public import ClassFieldTheory.GlobalClassFieldTheory.All
public import ClassFieldTheory.HasseArf
public import ClassFieldTheory.KroneckerWeber.All
public import ClassFieldTheory.KummerTheory.All
public import ClassFieldTheory.LocalClassFieldTheory.All
public import ClassFieldTheory.LocalFieldTheory.All
public import ClassFieldTheory.LubinTate.All
public import ClassFieldTheory.RamificationTheory.All
public import ClassFieldTheory.Theorems.All

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/















set_option autoImplicit false

/-!
# Class field theory

This is the canonical entry point for the class field theory library.
Its import closure is the complete production-library inventory.

The library contains local class field theory and global class field theory
for number fields, including the Hilbert product formula, general
power-residue reciprocity, and Gauss quadratic reciprocity, together with the
Hasse--Arf and Kronecker--Weber theorems. Shared valuation, ramification,
cohomology, Kummer, local-field, and Lubin--Tate infrastructure lives beside
those theories rather than under a theorem-specific directory.

For a smaller production dependency closure, import
`LocalClassFieldTheory`, `GlobalClassFieldTheory`, `HasseArf`, or
`KroneckerWeber` directly.
-/
