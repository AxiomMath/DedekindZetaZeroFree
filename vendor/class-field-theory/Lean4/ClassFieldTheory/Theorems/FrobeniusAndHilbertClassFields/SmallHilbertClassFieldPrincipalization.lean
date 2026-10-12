module

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
# Principalization in the small Hilbert class field

The principal ideal theorem says that extension to the Hilbert class field
makes every integral ideal of the base number field principal.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- Every integral ideal becomes principal in a small Hilbert class field. -/
theorem ideals_becomePrincipalInSmallHilbertClassField
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E) :
    ∀ I : Ideal (𝓞 K),
      (I.map (algebraMap (𝓞 K) (𝓞 E))).IsPrincipal := by
  exact GlobalClassFieldComparison.ideals_becomePrincipalInSmallHilbertClassField_of_isSmall K E hE

end ClassFieldTheory

end
