module

public import DedekindZetaZeroFree.RepresentationTheory.ClassicalGroups.SymmetricPowerCharacters
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.MaximalTorus
public import DedekindZetaZeroFree.Algebra.Units.LocalHomomorphismsAndPowers

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RepresentationTheory/SU2/SymmetricPower.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

open Finset Matrix
open scoped TensorProduct

namespace DedekindZetaZeroFree.TauCeti

namespace SU2

def toGL : SU2 →* GL (Fin 2) ℂ :=
  (Units.map (Submonoid.subtype _)).comp toUnits.toMonoidHom

@[simp]
theorem coe_toGL (g : SU2) :
    (toGL g : Matrix (Fin 2) (Fin 2) ℂ) = (g : Matrix (Fin 2) (Fin 2) ℂ) := (rfl)

theorem toGL_torusHom (z : Circle) :
    toGL (torusHom z) = diagGL ![Circle.toUnits z, (Circle.toUnits z)⁻¹] := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [coe_toGL, coe_torusHom, diagGL_coe]
  fin_cases i <;> fin_cases j <;>
    simp [torusMatrix_apply_zero_zero, torusMatrix_apply_zero_one, torusMatrix_apply_one_zero,
      torusMatrix_apply_one_one, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne,
      Units.val_inv_eq_inv_val]

variable (d : ℕ)

noncomputable def symPower : Representation ℂ SU2 (Sym[ℂ]^d (Fin 2 → ℂ)) :=
  (symPowerRep ℂ 2 d).comp toGL

@[simp]
theorem symPower_apply (g : SU2) : symPower d g = symPowerRep ℂ 2 d (toGL g) := (rfl)

theorem symPower_apply_tprod (g : SU2) (v : Fin d → (Fin 2 → ℂ)) :
    symPower d g (⨂ₛ[ℂ] i, v i) = ⨂ₛ[ℂ] i, (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v i := by
  simp only [symPower_apply, symPowerRep, Representation.symmetricPower_apply_tprod,
    stdRep_apply_apply, coe_toGL]

@[simp]
theorem finrank_symPower : Module.finrank ℂ (Sym[ℂ]^d (Fin 2 → ℂ)) = d + 1 := by
  rw [SymmetricPower.finrank_eq, Module.finrank_fin_fun, Nat.multichoose_two]

theorem character_symPower_torusHom (z : Circle) :
    (symPower d).character (torusHom z)
      = ∑ i ∈ range (d + 1), (z : ℂ) ^ i * ((z : ℂ)⁻¹) ^ (d - i) := by
  rw [Representation.character, symPower_apply, toGL_torusHom, ← Representation.character,
    char_symPowerRep_diagonal, eval_hsymm_fin_two]
  refine sum_congr rfl fun i _ => ?_
  simp

theorem character_symPower_torusHom_zpow (z : Circle) :
    (symPower d).character (torusHom z)
      = ∑ i ∈ range (d + 1), (z : ℂ) ^ (2 * (i : ℤ) - d) := by
  rw [character_symPower_torusHom]

  exact sum_congr rfl fun i hi =>
    pow_mul_inv_pow_eq_zpow₀ (Circle.coe_ne_zero z) (Nat.lt_succ_iff.mp (mem_range.mp hi))

end SU2

end DedekindZetaZeroFree.TauCeti
