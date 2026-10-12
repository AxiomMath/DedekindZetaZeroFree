module

public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.All
public import ClassFieldTheory.GlobalClassFieldTheory.Cohomology.All
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.All
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.All
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.All

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Global class field theory

This aggregate imports the implementation modules for global Artin reciprocity,
the class-field correspondence, Hilbert and power-residue reciprocity, ideal
Artin maps, decomposition, and principalization.  Reader-facing statements are
collected in `ClassFieldTheory.Theorems.GlobalClassFieldTheory.All`.
-/
