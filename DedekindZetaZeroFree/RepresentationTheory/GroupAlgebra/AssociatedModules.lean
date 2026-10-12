module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import DedekindZetaZeroFree.RepresentationTheory.FiniteDimensional.CharactersAndKernels

/-
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/AsModule.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
-/

@[expose] public section

namespace DedekindZetaZeroFree.TauCeti

open CategoryTheory

open scoped MonoidAlgebra

@[simp]
theorem _root_.Representation.finrank_moduleCat_asModule
    {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    letI := ModuleCat.moduleOfAlgebraModule (k := k) (ModuleCat.of k[G] ρ.asModule)
    Module.finrank k (ModuleCat.of k[G] ρ.asModule) = Module.finrank k V := by
  let := ModuleCat.moduleOfAlgebraModule (k := k) (ModuleCat.of k[G] ρ.asModule)
  let e : (ModuleCat.of k[G] ρ.asModule) ≃ₗ[k] V :=
    { toFun := fun x ↦ ρ.asModuleEquiv x
      invFun := fun x ↦ ρ.asModuleEquiv.symm x
      left_inv := fun x ↦ by exact ρ.asModuleEquiv.toEquiv.left_inv x
      right_inv := fun x ↦ by exact ρ.asModuleEquiv.toEquiv.right_inv x
      map_add' := fun x y ↦ by exact ρ.asModuleEquiv.map_add x y
      map_smul' := fun r x ↦ by

        change ρ.asModuleEquiv (algebraMap k k[G] r • x) = r • ρ.asModuleEquiv x
        rw [Representation.asModuleEquiv_map_smul, ρ.asAlgebraHom.commutes]
        rfl }
  exact e.finrank_eq

namespace Representation

variable {k G V W : Type*} [CommSemiring k] [Monoid G]

variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]

variable {ρ : _root_.Representation k G V} {σ : _root_.Representation k G W}

@[simp]
theorem _root_.Representation.asModuleEquiv_apply (x : ρ.asModule) :
    ρ.asModuleEquiv x = (x : V) :=
  (rfl)

@[simp]
theorem _root_.Representation.asModuleEquiv_symm_apply (x : V) :
    ρ.asModuleEquiv.symm x = x :=
  (rfl)

@[simp]
theorem _root_.Representation.IntertwiningMap.equivLinearMapAsModule_apply
    (f : _root_.Representation.IntertwiningMap ρ σ)
    (x : ρ.asModule) :
    _root_.Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f x = (f (x : V) : W) :=
  (rfl)

@[simp]
theorem _root_.Representation.IntertwiningMap.equivLinearMapAsModule_symm_apply
    (f : ρ.asModule →ₗ[k[G]] σ.asModule) (v : V) :
    ((_root_.Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).symm f) v =
      σ.asModuleEquiv (f (ρ.asModuleEquiv.symm v)) :=
  (rfl)

end Representation

end DedekindZetaZeroFree.TauCeti
