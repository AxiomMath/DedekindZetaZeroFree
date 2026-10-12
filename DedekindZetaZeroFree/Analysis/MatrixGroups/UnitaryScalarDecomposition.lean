module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/Analysis/Matrix/UnitaryGroup/Basic.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

namespace Matrix

variable {n α : Type*} [Fintype n] [DecidableEq n] [CommRing α] [StarRing α]

@[simp]
theorem diagonal_mem_unitaryGroup_iff {d : n → α} :
    diagonal d ∈ unitaryGroup n α ↔ ∀ i, d i ∈ unitary α := by
  simp only [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal, ← diagonal_one, diagonal_eq_diagonal_iff, Pi.star_apply,
    Unitary.mem_iff_self_mul_star]

end Matrix

namespace DedekindZetaZeroFree.TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem _root_.Circle.coe_mem_unitary (z : Circle) : (z : ℂ) ∈ unitary ℂ :=
  Unitary.mem_iff_star_mul_self.mpr <| by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe, Complex.ofReal_one]

theorem _root_.Matrix.exists_circle_smul_mem_specialUnitaryGroup (U : Matrix.unitaryGroup n ℂ) :
    ∃ c : Circle, ((c : ℂ) • (U : Matrix n n ℂ)) ∈ Matrix.specialUnitaryGroup n ℂ := by

  have hunit : ∀ c : Circle, ((c : ℂ) • (U : Matrix n n ℂ)) ∈ Matrix.unitaryGroup n ℂ := fun c =>
    Unitary.smul_mem_of_mem c.coe_mem_unitary U.2
  rcases isEmpty_or_nonempty n with hn | hn
  ·
    exact ⟨1, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨hunit 1, Matrix.det_isEmpty⟩⟩
  · have hcard : (Fintype.card n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hnorm : ‖(U : Matrix n n ℂ).det‖ = 1 :=
      CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary U.2)
    obtain ⟨θ, hθ⟩ := Circle.exp_surjective
      (⟨(U : Matrix n n ℂ).det, mem_sphere_zero_iff_norm.mpr hnorm⟩ : Circle)
    have hdetU : (U : Matrix n n ℂ).det = Complex.exp ((θ : ℂ) * Complex.I) := by
      have := congrArg (fun z : Circle => (z : ℂ)) hθ
      rw [Circle.coe_exp] at this
      exact this.symm
    refine ⟨Circle.exp (-(θ / Fintype.card n)), Matrix.mem_specialUnitaryGroup_iff.mpr
      ⟨hunit _, ?_⟩⟩
    rw [Matrix.det_smul, Circle.coe_exp, hdetU, ← Complex.exp_nat_mul, ← Complex.exp_add,
      ← Complex.exp_zero]
    congr 1
    push_cast
    field_simp
    ring

end DedekindZetaZeroFree.TauCeti
