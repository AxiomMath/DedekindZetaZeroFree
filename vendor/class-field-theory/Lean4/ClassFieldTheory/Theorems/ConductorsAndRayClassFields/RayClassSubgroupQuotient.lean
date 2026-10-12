module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupQuotientEquiv

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Quotient form of ray-class subgroup reciprocity

The quotient of a ray class group by the subgroup defining a class field is
the Galois group of that field.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

/-- A ray-class realization identifies its prescribed quotient with its
finite abelian Galois group. -/
theorem rayClassSubgroup_quotientEquiv
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m))
    (R : RayClassSubgroupRealization K m H) :
    Nonempty ((RayClassGroup m ⧸ H) ≃* (R.extension ≃ₐ[K] R.extension)) := by
  exact ⟨rayClassSubgroupQuotientEquiv K m H R⟩

end ClassFieldTheory

end
