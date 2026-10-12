module

public import ClassFieldTheory.AbstractClassFieldTheory.Degree.All
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.All

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Abstract class field theory

Public root for abstract degree data, class formations, reciprocity, and the construction and
naturality of Artin maps. The public declarations live in the `ClassFormation` namespace. This
library is independent of local class field theory.

The representation-free degree, field, extension, and topological-generation
APIs are universe-polymorphic.  The boundary that uses Mathlib's `Rep ℤ G` is
necessarily universe zero because `Rep` currently places its coefficient ring
and acting group in the same universe; the affected source sections state that
constraint explicitly.
-/
