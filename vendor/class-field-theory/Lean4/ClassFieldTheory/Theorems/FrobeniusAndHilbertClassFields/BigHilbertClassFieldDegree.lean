module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
public import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-!
# Degree of the big Hilbert class field

The degree of any extension satisfying the intrinsic big-Hilbert-class-field
property is the order of the narrow ray class group.  The latter is the ray
class group for the modulus containing every real place and no finite prime.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- The big Hilbert class field has degree equal to the narrow class number. -/
theorem bigHilbertClassField_degree_eq_narrowClassGroup_card
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsBigHilbertClassField E) :
    Module.finrank K E =
      Nat.card (RayClassGroup (narrowRayClassModulus K)) := by
  calc
    Module.finrank K E = Nat.card (RayClass.NarrowClassGroup K) :=
      GlobalClassFieldComparison.bigHilbertClassField_degree_eq_narrowClassGroup_card_of_isBig K E hE
    _ = Nat.card (RayClassGroup (narrowRayClassModulus K)) :=
      (Nat.card_congr
        (GlobalClassFieldComparison.narrowRayClassGroupEquivNarrowClassGroup K).toEquiv).symm

end ClassFieldTheory

end
