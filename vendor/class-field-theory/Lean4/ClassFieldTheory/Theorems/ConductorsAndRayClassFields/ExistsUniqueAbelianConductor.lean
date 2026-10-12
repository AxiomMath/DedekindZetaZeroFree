module

public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.ExistsAbelianConductor
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.IsAbelianConductorUnique
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Unique existence of the abelian conductor

Existence of a least ray-class-field modulus and uniqueness of any modulus
with the same universal property combine into a unique-existence statement.
-/

namespace ClassFieldTheory

/-- The conductor of a finite abelian extension of number fields exists
uniquely. -/
theorem existsUnique_abelianConductor
    (K : Type) [Field K] [NumberField K]
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] :
    ∃! c : RayClassModulus K, IsAbelianConductor K L c := by
  obtain ⟨c, hc⟩ := exists_abelianConductor K L
  exact ⟨c, hc, fun d hd => hd.unique hc⟩

end ClassFieldTheory
