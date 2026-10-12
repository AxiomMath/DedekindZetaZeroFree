module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.All
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.All
public import ClassFieldTheory.Definitions.GlobalClassFieldTheory.All
public import ClassFieldTheory.Definitions.HasseArf.All
public import ClassFieldTheory.Definitions.HilbertSymbols.All
public import ClassFieldTheory.Definitions.LocalClassFieldTheory.All
public import ClassFieldTheory.Definitions.NormTheorems.All

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/









set_option autoImplicit false

/-!
# Class field theory definitions

Reader-facing vocabulary used by the headline theorem modules.  Primitive
leaves import Mathlib only; derived leaves import only the prerequisite
definition leaves.  Topic-level `All` modules and this root module are
aggregation-only, and no public definition imports an implementation module.
-/
