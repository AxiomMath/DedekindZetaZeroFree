module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.SymmetricPower
public import Mathlib.Analysis.Real.Pi.Irrational
public import DedekindZetaZeroFree.Algebra.LinearAlgebra.DiagonalEigenspaces

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RepresentationTheory/SU2/Weight.lean`. Original Apache-2.0 copyright and authors retained.
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

variable (d : ℕ)

noncomputable def weightBasis : Module.Basis (Fin (d + 1)) ℂ (Sym[ℂ]^d(Fin 2 → ℂ)) :=
  ((Pi.basisFun ℂ (Fin 2)).symmetricPower d).reindex (symFinTwoEquiv d)

theorem weightBasis_apply (i : Fin (d + 1)) :
    weightBasis d i =
      (Pi.basisFun ℂ (Fin 2)).symmetricPower d ((symFinTwoEquiv d).symm i) :=
  Module.Basis.reindex_apply _ _ _

theorem exists_weightBasis_eq_tprod (i : Fin (d + 1)) :
    ∃ f : Fin d → Fin 2, weightBasis d i = ⨂ₛ[ℂ] j, Pi.basisFun ℂ (Fin 2) (f j) := by
  obtain ⟨f, hf⟩ := DedekindZetaZeroFree.TauCeti.Sym.ofFn_surjective ((symFinTwoEquiv d).symm i)
  exact ⟨f, by rw [weightBasis_apply, ← hf, Module.Basis.symmetricPower_apply,
    SymmetricPower.tprodOfSym_ofFn]⟩

def weight (i : Fin (d + 1)) : ℤ := 2 * (i : ℕ) - (d : ℤ)

theorem weight_def (i : Fin (d + 1)) : weight d i = 2 * (i : ℕ) - (d : ℤ) := (rfl)

@[simp]
theorem weight_zero : weight d 0 = -(d : ℤ) := by simp [weight_def]

@[simp]
theorem weight_last : weight d (Fin.last d) = (d : ℤ) := by
  rw [weight_def, Fin.val_last]
  ring

theorem weight_injective : Function.Injective (weight d) := by
  intro i j hij
  rw [weight_def, weight_def] at hij
  exact Fin.ext (by omega)

theorem symPower_torusHom_weightBasis (z : Circle) (i : Fin (d + 1)) :
    symPower d (torusHom z) (weightBasis d i) = (z : ℂ) ^ weight d i • weightBasis d i := by
  have hi : (i : ℕ) ≤ d := Nat.lt_succ_iff.mp i.isLt
  rw [weightBasis_apply, symPower_apply, toGL_torusHom,
    Representation.symmetricPower_apply,
    Module.Basis.map_symmetricPower_of_apply (Pi.basisFun ℂ (Fin 2)) _
      (fun j => ((![Circle.toUnits z, (Circle.toUnits z)⁻¹] j : ℂˣ) : ℂ))
      (stdRep_diagGL_apply_basisFun _)]
  congr 1

  rw [weight_def, ← pow_mul_inv_pow_eq_zpow₀ (Circle.coe_ne_zero z) hi]
  simp [coe_symFinTwoEquiv_symm_apply]

noncomputable def genericTorus : Circle := Circle.exp 1

private theorem coe_genericTorus_zpow_injective :
    Function.Injective fun m : ℤ => (genericTorus : ℂ) ^ m := by
  intro m n hmn
  have h : (genericTorus ^ m : Circle) = genericTorus ^ n :=
    Subtype.ext (by simpa only [Circle.coe_zpow] using hmn)
  rw [genericTorus, ← Circle.exp_intCast_mul, ← Circle.exp_intCast_mul, mul_one, mul_one] at h
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.1 h
  rcases eq_or_ne k 0 with rfl | hk0
  · have hmn' : (m : ℝ) = (n : ℝ) := by simpa using hk
    exact_mod_cast hmn'
  · refine absurd ?_ ((irrational_pi.intCast_mul (m := 2 * k) (by omega)).ne_int (m - n))
    push_cast
    linear_combination -hk

private theorem coe_genericTorus_zpow_weight_injective :
    Function.Injective fun i : Fin (d + 1) => (genericTorus : ℂ) ^ weight d i :=
  fun _ _ h => weight_injective d (coe_genericTorus_zpow_injective h)

variable {d}

theorem weightBasis_mem_of_repr_ne_zero {W : Submodule ℂ (Sym[ℂ]^d(Fin 2 → ℂ))}
    (hW : ∀ (z : Circle) (v : Sym[ℂ]^d(Fin 2 → ℂ)), v ∈ W → symPower d (torusHom z) v ∈ W)
    {w : Sym[ℂ]^d(Fin 2 → ℂ)} (hw : w ∈ W) {i : Fin (d + 1)}
    (hi : (weightBasis d).repr w i ≠ 0) : weightBasis d i ∈ W :=
  (weightBasis d).self_mem_of_repr_ne_zero (symPower_torusHom_weightBasis d genericTorus)
    (coe_genericTorus_zpow_weight_injective d) (hW genericTorus) hw hi

theorem eq_span_weightBasis_mem {W : Submodule ℂ (Sym[ℂ]^d(Fin 2 → ℂ))}
    (hW : ∀ (z : Circle) (v : Sym[ℂ]^d(Fin 2 → ℂ)), v ∈ W → symPower d (torusHom z) v ∈ W) :
    W = Submodule.span ℂ {v | ∃ i : Fin (d + 1), weightBasis d i = v ∧ v ∈ W} :=
  (weightBasis d).eq_span_self_mem (symPower_torusHom_weightBasis d genericTorus)
    (coe_genericTorus_zpow_weight_injective d) (hW genericTorus)

end SU2

end DedekindZetaZeroFree.TauCeti
