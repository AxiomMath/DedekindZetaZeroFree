module

public import ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation
public import ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization
public import ClassFieldTheory.LubinTate.FormalModule.Intertwiner
public import ClassFieldTheory.LubinTate.FormalModule.LinearTerm
public import ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient
public import ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection
public import ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner
public import ClassFieldTheory.LubinTate.FormalModule.Reduction
public import ClassFieldTheory.LubinTate.FormalModule.Series
public import ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup
public import ClassFieldTheory.LubinTate.FormalModule.StandardSeries

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/













set_option autoImplicit false

/-!
# Lubin--Tate formal modules

Public aggregate for the formal-series constructions used by Lubin--Tate
theory: composition, linear terms, intertwiners, coefficient equations,
reduction, the standard Lubin--Tate series, and the coefficientwise recursive
existence-and-uniqueness construction, including the resulting standard
commutative formal group and its coefficient-ring endomorphisms.
-/
