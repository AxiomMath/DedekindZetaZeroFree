module

public import ClassFieldTheory.LocalClassFieldTheory.Kummer.CanonicalKummerNorm
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.KummerExponentTower
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.KummerNormPowerClassDegree
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertExponentCompatibility
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairing
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairingNondegeneracy
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbol
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbolLaws
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.MathlibHilbertPairing
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.MaximalLocalKummerPairing
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/














set_option autoImplicit false

/-!
# Local Kummer reciprocity

Aggregate for the local Hilbert symbol, its laws, and the maximal local Kummer
pairing, including the tame power-residue formula.
-/
