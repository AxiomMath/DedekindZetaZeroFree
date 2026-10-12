module

public import ClassFieldTheory.LubinTate.FiniteLevel.ChangedLevelCompositum
public import ClassFieldTheory.LubinTate.FiniteLevel.ChangedPrimitiveEvaluation
public import ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer
public import ClassFieldTheory.LubinTate.FiniteLevel.CompletedEvaluation
public import ClassFieldTheory.LubinTate.FiniteLevel.CompletedIterates
public import ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial
public import ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameterFiltration
public import ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters
public import ClassFieldTheory.LubinTate.FiniteLevel.GaloisParameterFiltration
public import ClassFieldTheory.LubinTate.FiniteLevel.HerbrandFormula
public import ClassFieldTheory.LubinTate.FiniteLevel.HigherUnitLevelEquiv
public import ClassFieldTheory.LubinTate.FiniteLevel.LevelAbelian
public import ClassFieldTheory.LubinTate.FiniteLevel.LevelAutomorphisms
public import ClassFieldTheory.LubinTate.FiniteLevel.LevelFieldTower
public import ClassFieldTheory.LubinTate.FiniteLevel.LevelValuation
public import ClassFieldTheory.LubinTate.FiniteLevel.LocalUpperRamification
public import ClassFieldTheory.LubinTate.FiniteLevel.LowerRamification
public import ClassFieldTheory.LubinTate.FiniteLevel.LowerRamificationFormula
public import ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup
public import ClassFieldTheory.LubinTate.FiniteLevel.NormUniformizer
public import ClassFieldTheory.LubinTate.FiniteLevel.ParameterCongruence
public import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveAction
public import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement
public import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein
public import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot
public import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveTorsion
public import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer
public import ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField
public import ClassFieldTheory.LubinTate.FiniteLevel.UpperRamification

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/































set_option autoImplicit false

/-!
# General finite-level Lubin--Tate theory

Public aggregate for the characteristic-independent standard division
polynomials, primitive torsion fields, analytic formal-module action, explicit
finite Galois parameterization, integral-closure valuation, ramification
filtrations and their Herbrand formula, level-field tower, and the norm of a
primitive uniformizer.  It also exports stability of a standard level under
a principal-unit change of its defining uniformizer.
-/
