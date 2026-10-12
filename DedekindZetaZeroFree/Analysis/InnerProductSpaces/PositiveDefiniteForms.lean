module

public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/Analysis/InnerProductSpace/PositiveDefinite.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open RCLike
open scoped InnerProductSpace

namespace DedekindZetaZeroFree.TauCeti

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

theorem exists_continuousLinearEquiv_inner_map_map (S : V →L[𝕜] V)
    (hsymm : (S : V →ₗ[𝕜] V).IsSymmetric) (hpos : ∀ v : V, v ≠ 0 → 0 < re ⟪S v, v⟫_𝕜) :
    ∃ e : V ≃L[𝕜] V, ∀ x y : V, ⟪S (e x), e y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  classical
  set n := Module.finrank 𝕜 V with hn
  set b := hsymm.eigenvectorBasis hn.symm
  set lam := hsymm.eigenvalues hn.symm
  have hSb : ∀ i, S (b i) = (lam i : 𝕜) • b i := fun i ↦
    hsymm.apply_eigenvectorBasis hn.symm i
  have hbb : ∀ i j, ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal

  have hlam : ∀ i, 0 < lam i := fun i ↦ by
    have h := hpos (b i) (b.orthonormal.ne_zero i)
    rw [hSb i, inner_smul_left, hbb i i] at h
    simpa using h

  set w : Fin n → 𝕜 := fun i ↦ ((Real.sqrt (lam i))⁻¹ : ℝ) with hwdef
  have hw : ∀ i, IsUnit (w i) := fun i ↦ by
    refine isUnit_iff_ne_zero.mpr ?_
    simp [hwdef, Real.sqrt_eq_zero', (hlam i).not_ge]
  set el : V ≃ₗ[𝕜] V := b.toBasis.equiv (b.toBasis.isUnitSMul hw) (Equiv.refl (Fin n)) with heldef
  set e : V ≃L[𝕜] V := el.toContinuousLinearEquiv with hedef
  have he' : ∀ i, e (b.toBasis i) = w i • b.toBasis i := fun i ↦ by
    simp only [hedef, heldef, LinearEquiv.coe_toContinuousLinearEquiv',
      Module.Basis.equiv_apply, Equiv.refl_apply, Module.Basis.isUnitSMul_apply]
  have he : ∀ i, e (b i) = w i • b i := by simpa only [b.coe_toBasis] using he'
  have hkey : ∀ i j, ⟪S (e (b i)), e (b j)⟫_𝕜 = if i = j then 1 else 0 := fun i j ↦ by
    rw [he i, he j, map_smul, hSb i, smul_smul, inner_smul_left, inner_smul_right, hbb i j]
    rcases eq_or_ne i j with rfl | hij
    · have hr : ((Real.sqrt (lam i))⁻¹ * lam i * (Real.sqrt (lam i))⁻¹ : ℝ) = 1 := by
        have hne : Real.sqrt (lam i) ≠ 0 := (Real.sqrt_pos.mpr (hlam i)).ne'
        field_simp
        exact (Real.sq_sqrt (hlam i).le).symm
      rw [ite_eq_left rfl, mul_one, hwdef, ← RCLike.ofReal_mul, conj_ofReal, ← RCLike.ofReal_mul,
        hr, RCLike.ofReal_one]
    · simp [hij]

  refine ⟨e, fun x y ↦ ?_⟩
  rw [← b.sum_inner_mul_inner x y]
  conv_lhs => rw [← b.sum_repr' x, ← b.sum_repr' y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hkey]
  simp [inner_conj_symm, mul_comm]

end DedekindZetaZeroFree.TauCeti
