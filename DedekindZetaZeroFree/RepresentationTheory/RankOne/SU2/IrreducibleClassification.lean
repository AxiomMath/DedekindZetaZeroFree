module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import DedekindZetaZeroFree.RepresentationTheory.Compact.Characters.Orthogonality
public import DedekindZetaZeroFree.RepresentationTheory.Compact.UnitaryRepresentativeFunctions
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.BorelMeasurability
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.CharacterDensity
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.SymmetricPowerIrreducibility
public import DedekindZetaZeroFree.Analysis.MultilinearMaps.FiniteDimensionalContinuity

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/SU2/Exhaustion.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open Matrix
open scoped InnerProductSpace TensorProduct

namespace DedekindZetaZeroFree.TauCeti

namespace SU2

variable (d : ℕ)

noncomputable def weightEquiv : Sym[ℂ]^d(Fin 2 → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (d + 1)) :=
  (weightBasis d).equiv (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis (Equiv.refl _)

noncomputable def symPowerModel : ContRepresentation ℂ SU2 (EuclideanSpace ℂ (Fin (d + 1))) :=
  .ofMonoidHom
    { toFun g := LinearMap.toContinuousLinearMap ((weightEquiv d).conj (symPower d g))
      map_one' := by ext x; simp [LinearEquiv.conj_apply]
      map_mul' g h := by ext x; simp [LinearEquiv.conj_apply] }

@[simp]
theorem weightEquiv_weightBasis (i : Fin (d + 1)) :
    weightEquiv d (weightBasis d i) = EuclideanSpace.single i 1 := by
  rw [weightEquiv, Module.Basis.equiv_apply, OrthonormalBasis.coe_toBasis,
    Equiv.refl_apply, EuclideanSpace.basisFun_apply]

@[simp]
theorem weightEquiv_symm_single (i : Fin (d + 1)) :
    (weightEquiv d).symm (EuclideanSpace.single i 1) = weightBasis d i :=
  (LinearEquiv.symm_apply_eq _).2 (weightEquiv_weightBasis d i).symm

@[simp]
theorem symPowerModel_apply (g : SU2) (x : EuclideanSpace ℂ (Fin (d + 1))) :
    symPowerModel d g x = weightEquiv d (symPower d g ((weightEquiv d).symm x)) := (rfl)

private theorem continuous_mulVec (w : Fin 2 → ℂ) :
    Continuous fun g : SU2 ↦ (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ w := by
  refine continuous_pi fun i ↦ ?_
  simp only [Matrix.mulVec, dotProduct]
  refine continuous_finsetSum _ fun j _ ↦ Continuous.mul ?_ continuous_const
  exact (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

private theorem continuous_weightEquiv_symPower_tprod (v : Fin d → (Fin 2 → ℂ)) :
    Continuous fun g : SU2 ↦ weightEquiv d (symPower d g (⨂ₛ[ℂ] j, v j)) := by
  have hΦ : Continuous
      ((weightEquiv d).toLinearMap.compMultilinearMap (SymmetricPower.tprod ℂ)) :=
    MultilinearMap.continuous_of_finiteDimensional _
  have hv : Continuous fun g : SU2 ↦ fun j ↦ (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v j :=
    continuous_pi fun j ↦ continuous_mulVec (v j)
  exact (hΦ.comp hv).congr fun g ↦ by simp

private theorem continuous_weightEquiv_symPower (x : Sym[ℂ]^d(Fin 2 → ℂ)) :
    Continuous fun g : SU2 ↦ weightEquiv d (symPower d g x) := by
  have hb : ∀ i : Fin (d + 1),
      Continuous fun g : SU2 ↦ weightEquiv d (symPower d g (weightBasis d i)) := fun i ↦ by
    obtain ⟨f, hf⟩ := exists_weightBasis_eq_tprod d i
    rw [hf]
    exact continuous_weightEquiv_symPower_tprod d _
  have hx : (fun g : SU2 ↦ weightEquiv d (symPower d g x)) =
      fun g : SU2 ↦ ∑ i, (weightBasis d).repr x i •
        weightEquiv d (symPower d g (weightBasis d i)) := by
    funext g
    calc weightEquiv d (symPower d g x)
        = weightEquiv d (symPower d g (∑ i, (weightBasis d).repr x i • weightBasis d i)) := by
          rw [(weightBasis d).sum_repr x]
      _ = ∑ i, (weightBasis d).repr x i • weightEquiv d (symPower d g (weightBasis d i)) := by
          simp only [map_sum, map_smul]
  rw [hx]
  exact continuous_finsetSum _ fun i _ ↦
    (continuous_const_smul ((weightBasis d).repr x i)).comp (hb i)

theorem continuous_symPowerModel : Continuous (symPowerModel d) :=
  continuous_clm_apply.2 fun y ↦ by
    simpa using continuous_weightEquiv_symPower d ((weightEquiv d).symm y)

noncomputable def symPowerModelEquiv : (symPower d).Equiv (symPowerModel d).toRepresentation :=
  Representation.Equiv.mk (weightEquiv d) fun g ↦ LinearMap.ext fun v ↦ by
    simp [_root_.ContRepresentation.toMonoidHom_apply]

@[simp]
theorem symPowerModelEquiv_toLinearEquiv :
    (symPowerModelEquiv d).toLinearEquiv = weightEquiv d := by
  rw [symPowerModelEquiv, Representation.Equiv.toLinearEquiv_mk']

@[simp]
theorem symPowerModelEquiv_apply (x : Sym[ℂ]^d(Fin 2 → ℂ)) :
    symPowerModelEquiv d x = weightEquiv d x := by
  rw [symPowerModelEquiv, Representation.Equiv.mk_apply]

@[simp]
theorem character_symPowerModel :
    ContRepresentation.character (symPowerModel d) (continuous_symPowerModel d) =
      symPowerCharacter d :=
  ContinuousMap.ext fun g ↦ by
    rw [symPowerCharacter_apply, Representation.char_iso (symPowerModelEquiv d)]
    exact congrFun (ContRepresentation.coe_character _ _) g

theorem isIrreducible_symPowerModel :
    Representation.IsIrreducible (symPowerModel d).toRepresentation :=
  Representation.isIrreducible_of_linearEquiv (weightEquiv d)
    (fun g v ↦ by simp [_root_.ContRepresentation.toMonoidHom_apply])
    (isIrreducible_symPower d)

end SU2

end DedekindZetaZeroFree.TauCeti
