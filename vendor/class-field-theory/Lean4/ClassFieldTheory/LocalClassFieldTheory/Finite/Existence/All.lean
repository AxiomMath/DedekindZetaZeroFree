module

public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.CharacteristicZero
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.Classification
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.CyclotomicKummerDescent
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.EqualCharacteristic
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.EqualCharacteristicDominatingExtension
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.FiniteUnramifiedField
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.KummerNormOpen
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.LocalAbsoluteData
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.LubinTateUniformizerDiagonal
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.MathlibFieldClassification
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.MaximalKummerNorm
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupRingEquiv
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupSurjectivity
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkChosenFiniteAbelianFields
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkChosenFiniteAbelianNorms
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkFiniteAbelianFields
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkFiniteAbelianNorms
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkIntermediateFields
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkLocalClassification
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkOpenSubgroups
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkSeparableClosure
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardDominatingExtension
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardLubinTate
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardSubgroupIntersection
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedLubinTateDiagonal
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormContainment
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnshrinkFiniteAbelianFields

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
































set_option autoImplicit false

/-!
# Finite local existence theorem

The ordinary norm-subgroup assignment is an order embedding into the
opposite poset of native open finite-index subgroups.  Kummer theory in
characteristic zero and transported Lubin--Tate levels in positive
characteristic prove the existing characteristic-specific order
isomorphisms.  The canonical standard Lubin--Tate construction now also
provides a characteristic-independent finite abelian factor with its exact
norm subgroup.
-/
