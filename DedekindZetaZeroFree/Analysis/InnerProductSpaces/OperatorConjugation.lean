module

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/Analysis/InnerProductSpace/Conjugation.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open scoped InnerProductSpace

namespace DedekindZetaZeroFree.TauCeti

section Conjugation

variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

noncomputable def conjugation (e : OrthonormalBasis ι 𝕜 V) (x : V) : V :=
  ∑ i, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 • e i

variable (e : OrthonormalBasis ι 𝕜 V)

theorem conjugation_apply (x : V) :
    conjugation e x = ∑ i, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 • e i :=
  (rfl)

@[simp]
theorem inner_conjugation (x : V) (j : ι) :
    ⟪e j, conjugation e x⟫_𝕜 = (starRingEnd 𝕜) ⟪e j, x⟫_𝕜 := by
  classical
  have h : ∀ i, ⟪e j, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 • e i⟫_𝕜 =
      if i = j then (starRingEnd 𝕜) ⟪e j, x⟫_𝕜 else 0 := fun i ↦ by
    rw [inner_smul_right, orthonormal_iff_ite.mp e.orthonormal]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [conjugation_apply, inner_sum]
  simp only [h]
  simp

@[simp]
theorem conjugation_zero : conjugation e (0 : V) = 0 := by
  simp [conjugation_apply]

@[simp]
theorem conjugation_add (x y : V) :
    conjugation e (x + y) = conjugation e x + conjugation e y := by
  simp [conjugation_apply, inner_add_right, add_smul, Finset.sum_add_distrib]

@[simp]
theorem conjugation_smul (c : 𝕜) (x : V) :
    conjugation e (c • x) = (starRingEnd 𝕜) c • conjugation e x := by
  simp [conjugation_apply, inner_smul_right, Finset.smul_sum, smul_smul]

@[simp]
theorem conjugation_neg (x : V) : conjugation e (-x) = -conjugation e x := by
  simp [conjugation_apply, inner_neg_right, neg_smul, Finset.sum_neg_distrib]

@[simp]
theorem conjugation_sub (x y : V) :
    conjugation e (x - y) = conjugation e x - conjugation e y := by
  simp [conjugation_apply, inner_sub_right, sub_smul, Finset.sum_sub_distrib]

@[simp]
theorem conjugation_conjugation (x : V) : conjugation e (conjugation e x) = x := by
  have h : ∀ i, (starRingEnd 𝕜) ⟪e i, conjugation e x⟫_𝕜 = ⟪e i, x⟫_𝕜 := fun i ↦ by
    rw [inner_conjugation]; simp
  rw [conjugation_apply (x := conjugation e x)]
  simp only [h]
  exact e.sum_repr' x

@[simp]
theorem conjugation_basis (j : ι) : conjugation e (e j) = e j := by
  classical
  have h : ∀ i, (starRingEnd 𝕜) ⟪e i, e j⟫_𝕜 = ⟪e i, e j⟫_𝕜 := fun i ↦ by
    rw [orthonormal_iff_ite.mp e.orthonormal]
    split <;> simp
  rw [conjugation_apply]
  simp only [h]
  exact e.sum_repr' (e j)

@[simp]
theorem inner_conjugation_conjugation (x y : V) :
    ⟪conjugation e x, conjugation e y⟫_𝕜 = (starRingEnd 𝕜) ⟪x, y⟫_𝕜 := by
  have hxy : ⟪x, y⟫_𝕜 = ∑ i, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 * ⟪e i, y⟫_𝕜 := by
    conv_lhs => rw [← e.sum_repr' x]
    rw [sum_inner]
    simp [inner_smul_left]
  rw [conjugation_apply e x, sum_inner, hxy, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_smul_left, inner_conjugation]
  simp [mul_comm]

@[simp]
theorem inner_conjugation_left_basis (x : V) (j : ι) :
    ⟪conjugation e x, e j⟫_𝕜 = ⟪e j, x⟫_𝕜 := by
  conv_lhs => rw [← conjugation_basis e j]
  rw [inner_conjugation_conjugation, inner_conj_symm]

@[simp]
theorem norm_conjugation (x : V) : ‖conjugation e x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜) (conjugation e x), norm_eq_sqrt_re_inner (𝕜 := 𝕜) x,
    inner_conjugation_conjugation]
  simp

end Conjugation

section ConjugateOperator

variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (e : OrthonormalBasis ι 𝕜 V)

noncomputable def conjCLM (A : V →L[𝕜] V) : V →L[𝕜] V :=
  LinearMap.mkContinuous
    { toFun x := conjugation e (A (conjugation e x))
      map_add' x y := by simp
      map_smul' c x := by simp } ‖A‖ fun x ↦ by
    simpa using A.le_opNorm (conjugation e x)

@[simp]
theorem conjCLM_apply (A : V →L[𝕜] V) (x : V) :
    conjCLM e A x = conjugation e (A (conjugation e x)) :=
  (rfl)

@[simp]
theorem conjCLM_one : conjCLM e 1 = 1 := by
  ext x
  simp

@[simp]
theorem conjCLM_mul (A B : V →L[𝕜] V) : conjCLM e (A * B) = conjCLM e A * conjCLM e B := by
  ext x
  simp

@[simp]
theorem conjCLM_conjCLM (A : V →L[𝕜] V) : conjCLM e (conjCLM e A) = A := by
  ext x
  simp

@[simp]
theorem conjCLM_zero : conjCLM e (0 : V →L[𝕜] V) = 0 := by
  ext x
  simp

@[simp]
theorem conjCLM_add (A B : V →L[𝕜] V) : conjCLM e (A + B) = conjCLM e A + conjCLM e B := by
  ext x
  simp

@[simp]
theorem conjCLM_neg (A : V →L[𝕜] V) : conjCLM e (-A) = -conjCLM e A := by
  ext x
  simp

@[simp]
theorem conjCLM_sub (A B : V →L[𝕜] V) : conjCLM e (A - B) = conjCLM e A - conjCLM e B := by
  ext x
  simp

@[simp]
theorem conjCLM_smul (c : 𝕜) (A : V →L[𝕜] V) : conjCLM e (c • A) = star c • conjCLM e A := by
  ext x
  simp [RCLike.star_def]

theorem norm_conjCLM_le (A : V →L[𝕜] V) : ‖conjCLM e A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

@[simp]
theorem norm_conjCLM (A : V →L[𝕜] V) : ‖conjCLM e A‖ = ‖A‖ :=
  le_antisymm (norm_conjCLM_le e A) <| by
    simpa using norm_conjCLM_le e (conjCLM e A)

theorem lipschitzWith_one_conjCLM : LipschitzWith 1 (conjCLM e) :=
  LipschitzWith.of_dist_le_mul fun A B ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← conjCLM_sub, norm_conjCLM]
    simp

end ConjugateOperator

end DedekindZetaZeroFree.TauCeti
