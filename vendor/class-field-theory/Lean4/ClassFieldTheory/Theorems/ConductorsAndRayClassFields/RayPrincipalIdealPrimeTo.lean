module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayPrincipalIdealSubgroup
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayPrincipalIdealMembership
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Ray-principal ideals are prime to the modulus

The local congruence condition makes the corresponding principal idèle
integral-unit-valued at every finite prime in the modulus support.
-/

open scoped Classical NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

universe u

/-- A ray-principal fractional ideal has zero exponent at every finite
prime in the modulus support. -/
theorem rayPrincipalIdealSubgroup_le_primeToIdeals
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) :
    rayPrincipalIdealSubgroup m ≤ rayClassPrimeToIdeals m := by
  intro I hI
  obtain ⟨x, hx, hIx⟩ := (mem_rayPrincipalIdealSubgroup_iff m I).1 hI
  intro v hv
  rw [← hIx, ← IdeleGroup.fractionalIdeal_principalIdele]
  change FractionalIdeal.count K v
      (((FractionalIdealGroup.factorization (K := K))
        (FiniteIdeleGroup.valuationVector
          (IdeleGroup.principalIdele K x).2) : FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
  rw [FractionalIdealGroup.count_factorization,
    FiniteIdeleGroup.valuationVector_apply]
  apply (FiniteIdeleGroup.localOrder_eq_zero_iff v
    ((IdeleGroup.principalIdele K x).2 v)).2
  apply RayClass.localHigherUnitGroup_le_integralUnits v (m.finitePart v)
  exact hx.1 v hv

end ClassFieldTheory

end
