module

public import DedekindZetaZeroFree.Algebra.SymmetricPower.TensorEmbedding

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/LinearAlgebra/SymmetricPower/Lift.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

open scoped TensorProduct

universe u v w

variable {R ι : Type u} {M : Type v} {N : Type w}

namespace SymmetricPower

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable (f : MultilinearMap R (fun _ : ι ↦ M) N)

theorem lift_rel (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) :
    addConGen (Rel R ι M) ≤ AddCon.ker (PiTensorProduct.lift f).toAddMonoidHom := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e m =>
      refine (AddCon.ker_rel _).2 ?_
      simp only [LinearMap.toAddMonoidHom_coe, PiTensorProduct.lift.tprod]
      exact (congrFun (congrArg DFunLike.coe (hf e)) m).symm

noncomputable def lift (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) : Sym[R] ι M →ₗ[R] N where
  toFun := (addConGen (Rel R ι M)).lift (PiTensorProduct.lift f).toAddMonoidHom (lift_rel f hf)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => (PiTensorProduct.lift f).map_smul r x

@[simp]
theorem lift_mk (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) (x : ⨂[R] (_ : ι), M) :
    lift f hf (mk R ι M x) = PiTensorProduct.lift f x :=
  AddCon.lift_mk' (lift_rel f hf) x

@[simp]
theorem lift_tprod (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) (m : ι → M) :
    lift f hf (⨂ₛ[R] i, m i) = f m := by
  rw [tprod, LinearMap.compMultilinearMap_apply, lift_mk, PiTensorProduct.lift.tprod]

@[ext]
theorem ext {g h : Sym[R] ι M →ₗ[R] N}
    (hgh : ∀ m : ι → M, g (⨂ₛ[R] i, m i) = h (⨂ₛ[R] i, m i)) : g = h := by
  refine LinearMap.ext_on (span_tprod_eq_top R ι M) ?_
  rintro _ ⟨m, rfl⟩
  exact hgh m

end SymmetricPower
