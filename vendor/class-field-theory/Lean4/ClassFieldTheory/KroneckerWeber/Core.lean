module

public import ClassFieldTheory.KroneckerWeber.LocalCyclotomicEmbedding
public import ClassFieldTheory.KroneckerWeber.RationalCyclotomicArithmeticReciprocity
public import ClassFieldTheory.KroneckerWeber.Final
public import ClassFieldTheory.KroneckerWeber.GlobalCompositumCyclotomicTarget
public import ClassFieldTheory.KroneckerWeber.GlobalCompositumGlobalEmbedding
public import ClassFieldTheory.KroneckerWeber.GlobalCompositumLeftFactors
public import ClassFieldTheory.KroneckerWeber.GlobalCompositumLocalizationEmbedding
public import ClassFieldTheory.KroneckerWeber.GlobalCompositumValuationInertiaBound
public import ClassFieldTheory.KroneckerWeber.GlobalCompositumValuedEmbedding
public import ClassFieldTheory.KroneckerWeber.GlobalPadicPrimePowInertiaBound
public import ClassFieldTheory.KroneckerWeber.RationalRayClassFieldCyclotomic
public import ClassFieldTheory.KroneckerWeber.RayClassComparison
public import ClassFieldTheory.KroneckerWeber.Setup
public import ClassFieldTheory.KroneckerWeber.UnramifiedCompositumSupport

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
















set_option autoImplicit false

/-!
# Kronecker--Weber

The reader-facing entry point for the local and global Kronecker--Weber
theorems.  Importing this module exposes both supported endpoints.
-/

/-!
# The global Kronecker--Weber theorem

Every finite abelian extension of `ℚ` is contained in a cyclotomic field.
The arithmetic construction and global degree estimate are kept in the
semantic support modules under `KroneckerWeber.Global`; this root exposes the
canonical theorem statement.
-/

noncomputable section

namespace KroneckerWeber

/-- **Global Kronecker--Weber.**

Every finite abelian extension of `ℚ` embeds in `ℚ(ζₙ)` for some positive
integer `n`.  Here `CyclotomicField n ℚ` is the concrete model of
`ℚ(ζₙ)`. -/
theorem exists_cyclotomicEmbedding
    (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L] :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) :=
  ⟨kroneckerWeberConductorCandidate (L := L),
    kroneckerWeberConductorCandidate_pos (L := L),
    ⟨kroneckerWeberCyclotomicEmbedding (L := L)⟩⟩

end KroneckerWeber

end
