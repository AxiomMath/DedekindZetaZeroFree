module

public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeSplitsCompletely
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Prime splitting in the small Hilbert class field

A finite prime splits completely in the Hilbert class field precisely when
its fractional ideal class is trivial.  Both sides use Mathlib's native
ideal-theoretic objects.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

/-- A finite prime splits completely in a small Hilbert class field exactly
when its fractional ideal is principal. -/
theorem finitePrime_splitsCompletelyInSmallHilbertClassField_iff_principal
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E)
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePrimeSplitsCompletely K E v ↔
      finitePrimeFractionalIdeal v ∈
        (toPrincipalIdeal (𝓞 K) K).range := by
  exact GlobalClassFieldComparison.finitePrime_splitsCompletelyInSmallHilbertClassField_iff_principal_of_isSmall
    K E hE v

end ClassFieldTheory

end
