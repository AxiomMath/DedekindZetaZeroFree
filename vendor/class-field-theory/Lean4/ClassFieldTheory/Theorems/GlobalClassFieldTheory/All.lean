module

public import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianGlobalReciprocity
public import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianGlobalReciprocityQuotient
public import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianReciprocityQuotientEquivMk
public import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceLocalGlobalNormKernel
public import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceRayArtinNormKernel
public import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceRayArtinDecomposition
public import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceCompletionLocalArtin
public import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceRayArtinLocalValue
public import ClassFieldTheory.Theorems.GlobalClassFieldTheory.TopologicalGlobalReciprocity
public import ClassFieldTheory.Theorems.GlobalClassFieldTheory.MaximalAbelianGlobalArtin

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/












set_option autoImplicit false

/-!
# Global class field theory

This module collects finite ideal-theoretic reciprocity and the topological
maximal-abelian statements. The latter are proved via topological comparison
with the existing restricted-product implementation.
-/
