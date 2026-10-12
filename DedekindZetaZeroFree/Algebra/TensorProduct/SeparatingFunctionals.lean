module

public import DedekindZetaZeroFree.Algebra.TensorProduct.BasisAndBaseChange

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/LinearAlgebra/TensorProduct/Separation.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

open scoped TensorProduct

namespace DedekindZetaZeroFree.TauCeti

theorem tensor_eq_zero_of_forall_lid_rTensor_eq_zero
    {R M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Module.Projective R N]
    (f : ι → M →ₗ[R] R) (hf : ∀ m, (∀ i, f i m = 0) → m = 0)
    (x : M ⊗[R] N)
    (hx : ∀ i, TensorProduct.lid R N ((f i).rTensor N x) = 0) :
    x = 0 := by
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  simp only [map_zero]
  apply hf
  intro i
  exact (DFunLike.congr_fun ((f i).comp_tensorComponent φ) x).trans
    (by simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hx i, map_zero])

theorem tensor_eq_zero_of_forall_lid_map_eq_zero
    {R M N ι κ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Module.Projective R N]
    (f : ι → M →ₗ[R] R) (g : κ → N →ₗ[R] R)
    (hf : ∀ m, (∀ i, f i m = 0) → m = 0)
    (hg : ∀ n, (∀ j, g j n = 0) → n = 0)
    (x : M ⊗[R] N)
    (hx : ∀ i j, TensorProduct.lid R R (TensorProduct.map (f i) (g j) x) = 0) :
    x = 0 := by
  apply tensor_eq_zero_of_forall_lid_rTensor_eq_zero f hf x
  intro i
  apply hg
  intro j
  have hcomp : (g j).comp ((TensorProduct.lid R N).toLinearMap.comp
      (TensorProduct.map (f i) LinearMap.id)) =
      (TensorProduct.lid R R).toLinearMap.comp (TensorProduct.map (f i) (g j)) := by
    ext m n
    simp
  exact (DFunLike.congr_fun hcomp x).trans (hx i j)

end DedekindZetaZeroFree.TauCeti
