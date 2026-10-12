module

public import ClassFieldTheory.LocalFieldTheory.Padic.All

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Local field theory

Public root for reusable local-field infrastructure. This layer may depend on `ValuationTheory`,
but not on `RamificationTheory`, `ClassFormation`, or `LocalClassFieldTheory`.
-/
