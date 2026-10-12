module

public import ClassFieldTheory.AlgebraicNumberTheory.Adele.All
public import ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.All
public import ClassFieldTheory.AlgebraicNumberTheory.CompositumEmbedding
public import ClassFieldTheory.AlgebraicNumberTheory.FiniteAbelianCompositum
public import ClassFieldTheory.AlgebraicNumberTheory.Galois.All
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.All
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceAdicCompletionCongrEquiv
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivTopology
public import ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
public import ClassFieldTheory.AlgebraicNumberTheory.NumberField.All
public import ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.All
public import ClassFieldTheory.AlgebraicNumberTheory.QuadraticReciprocity
public import ClassFieldTheory.AlgebraicNumberTheory.Ramification.All
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.All
public import ClassFieldTheory.AlgebraicNumberTheory.SUnit.All
public import ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import ClassFieldTheory.AlgebraicNumberTheory.TensorProduct

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




















set_option autoImplicit false

/-!
# Algebraic number theory

Public root for the reusable global algebraic-number-theory layer used by
class field theory. It exports finite abelian composita, idèles and idèle
classes in extensions, normal-closure and splitting results, ray class groups,
S-units, and the ramification and degree results needed by global applications.
-/
