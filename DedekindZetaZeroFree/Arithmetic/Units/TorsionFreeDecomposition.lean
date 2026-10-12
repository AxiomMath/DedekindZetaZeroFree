module

public import DedekindZetaZeroFree.Arithmetic.Units.FundamentalDomainIntegration

@[expose] public section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Mechanical port of `LeanPool/Odlyzko/CompletedZeta/UnitDecomposition.lean`
from https://github.com/LeanPool/lean-pool at exact revision
`68aa6ee63d20ad76bcc15f595adfc72949991f06` (Lean 4.35.0-rc3, ported to rc2).
Original copyright and author attribution are retained above. Released under
Apache 2.0; the full license is in the repository root `LICENSE`.
Source changes: imports, module visibility syntax, namespace, and additional
multiplication/inverse formulas below the original declarations.
-/

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.Units
  dirichletUnitTheorem

namespace DedekindZetaZeroFree.Theta

open mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in

def unitExponentReindex :
    (Fin (rank K) → ℤ) ≃
      ({w : InfinitePlace K // w ≠ w₀} → ℤ) where
  toFun f i := f (equivFinRank.symm i)
  invFun z i := z (equivFinRank i)
  left_inv f := by
    simp
  right_inv z := by
    simp

theorem fundamentalUnitForShift_unitExponentReindex
    (f : Fin (rank K) → ℤ) :
    fundamentalUnitForShift (unitExponentReindex K f) =
      ∏ i, fundSystem K i ^ f i := by
  classical
  exact (Fintype.prod_equiv
    (mixedEmbedding.fundamentalCone.equivFinRank (K := K))
    (fun i ↦ fundSystem K i ^ f i)
    (fun w ↦ fundSystem K (equivFinRank.symm w) ^
      unitExponentReindex K f w)
    (fun _ ↦ by simp [unitExponentReindex])).symm

noncomputable def unitDecompositionMap :
    torsion K × ({w : InfinitePlace K // w ≠ w₀} → ℤ) →
      (𝓞 K)ˣ :=
  fun p ↦ p.1 * fundamentalUnitForShift p.2

theorem bijective_unitDecompositionMap :
    Function.Bijective (unitDecompositionMap K) := by
  classical
  constructor
  · rintro ⟨ζ, z⟩ ⟨ζ', z'⟩ h
    let f := (unitExponentReindex K).symm z
    let f' := (unitExponentReindex K).symm z'
    have hfund : fundamentalUnitForShift z =
        ∏ i, fundSystem K i ^ f i := by
      rw [← fundamentalUnitForShift_unitExponentReindex K f]
      simp [f]
    have hfund' : fundamentalUnitForShift z' =
        ∏ i, fundSystem K i ^ f' i := by
      rw [← fundamentalUnitForShift_unitExponentReindex K f']
      simp [f']
    have hu := exist_unique_eq_mul_prod K (unitDecompositionMap K (ζ, z))
    have h₁ : unitDecompositionMap K (ζ, z) =
        ζ * ∏ i, fundSystem K i ^ f i := by
      rw [unitDecompositionMap, hfund]
    have h₂ : unitDecompositionMap K (ζ, z) =
        ζ' * ∏ i, fundSystem K i ^ f' i := by
      calc
        unitDecompositionMap K (ζ, z) =
            unitDecompositionMap K (ζ', z') := h
        _ = ζ' * ∏ i, fundSystem K i ^ f' i := by
          rw [unitDecompositionMap, hfund']
    have hp : (ζ, f) = (ζ', f') := hu.unique h₁ h₂
    apply Prod.ext
    · simp_all
    · apply (unitExponentReindex K).symm.injective
      grind
  · intro u
    obtain ⟨⟨ζ, f⟩, hu, _⟩ := exist_unique_eq_mul_prod K u
    refine ⟨(ζ, unitExponentReindex K f), ?_⟩
    rw [unitDecompositionMap,
      fundamentalUnitForShift_unitExponentReindex]
    simp_all

open scoped Classical in

def unitDecompositionEquiv :
    torsion K × ({w : InfinitePlace K // w ≠ w₀} → ℤ) ≃
      (𝓞 K)ˣ :=
  Equiv.ofBijective (unitDecompositionMap K)
    (bijective_unitDecompositionMap K)

@[simp]
theorem unitDecompositionEquiv_apply
    (p : torsion K × ({w : InfinitePlace K // w ≠ w₀} → ℤ)) :
    unitDecompositionEquiv K p =
      p.1 * fundamentalUnitForShift p.2 :=
  rfl

@[simp]
theorem fundamentalUnitForShift_zero :
    fundamentalUnitForShift (K := K) 0 = 1 := by
  classical
  simp [fundamentalUnitForShift]

theorem fundamentalUnitForShift_add
    (z z' : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    fundamentalUnitForShift (z + z') =
      fundamentalUnitForShift z * fundamentalUnitForShift z' := by
  classical
  simp [fundamentalUnitForShift, zpow_add, Finset.prod_mul_distrib]

@[simp]
theorem fundamentalUnitForShift_neg
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    fundamentalUnitForShift (-z) = (fundamentalUnitForShift z)⁻¹ := by
  classical
  simp [fundamentalUnitForShift, Finset.prod_inv_distrib]

@[simp]
theorem unitDecompositionEquiv_symm_apply_mul
    (ζ : torsion K) (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    (unitDecompositionEquiv K).symm (ζ * fundamentalUnitForShift z) =
      (ζ, z) := by
  exact (unitDecompositionEquiv K).symm_apply_apply (ζ, z)

@[simp]
theorem unitDecompositionEquiv_symm_apply_fundamentalUnitForShift
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    (unitDecompositionEquiv K).symm (fundamentalUnitForShift z) = (1, z) := by
  simpa using unitDecompositionEquiv_symm_apply_mul K 1 z

theorem unitDecompositionEquiv_mul
    (p q : torsion K × ({w : InfinitePlace K // w ≠ w₀} → ℤ)) :
    unitDecompositionEquiv K (p.1 * q.1, p.2 + q.2) =
      unitDecompositionEquiv K p * unitDecompositionEquiv K q := by
  simp only [unitDecompositionEquiv_apply, fundamentalUnitForShift_add,
    Subgroup.coe_mul]
  ac_rfl

@[simp]
theorem unitDecompositionEquiv_symm_mul (u v : (𝓞 K)ˣ) :
    (unitDecompositionEquiv K).symm (u * v) =
      (((unitDecompositionEquiv K).symm u).1 *
        ((unitDecompositionEquiv K).symm v).1,
       ((unitDecompositionEquiv K).symm u).2 +
        ((unitDecompositionEquiv K).symm v).2) := by
  apply (unitDecompositionEquiv K).injective
  simp only [Equiv.apply_symm_apply, unitDecompositionEquiv_mul]

end DedekindZetaZeroFree.Theta

end
