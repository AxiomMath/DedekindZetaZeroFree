module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Existence of the class field of a ray-class subgroup

Every subgroup of an ideal-theoretic ray class group is the kernel of the
Frobenius-normalized Artin map of a finite abelian extension.  The statement
uses ideal classes; the proof transports the existing idelic reciprocity
construction to that interface.
-/

open scoped Classical NumberField

noncomputable section

namespace ClassFieldTheory

/-- Every ray-class subgroup has a finite abelian class-field realization. -/
theorem rayClassSubgroup_existence
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m)) :
    Nonempty (RayClassSubgroupRealization K m H) := by
  exact GlobalClassFieldComparison.rayClassSubgroup_existence K m H

end ClassFieldTheory

end
