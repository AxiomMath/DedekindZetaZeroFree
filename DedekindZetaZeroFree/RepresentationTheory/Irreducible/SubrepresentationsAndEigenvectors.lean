module

public import Mathlib.RepresentationTheory.Semisimple
public import DedekindZetaZeroFree.RepresentationTheory.Subrepresentations.Restriction
public import Mathlib.RingTheory.SimpleModule.Rank
public import Mathlib.RingTheory.FiniteLength
public import DedekindZetaZeroFree.Algebra.LocalRings.IdempotentsAndUnits
public import DedekindZetaZeroFree.Algebra.SemisimpleModules.AnnihilatorsAndEndomorphisms
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import DedekindZetaZeroFree.Algebra.TensorProduct.SeparatingFunctionals

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RepresentationTheory/Irreducible.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

open DedekindZetaZeroFree.TauCeti
open scoped TensorProduct

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

open scoped MonoidAlgebra in

theorem IsIrreducible.nontrivial {ρ : Representation k G V}
    (h : ρ.IsIrreducible) : Nontrivial V :=
  have _ : ρ.IsIrreducible := h
  have _ := IsSimpleModule.nontrivial k[G] ρ.asModule
  ρ.asModuleEquiv.symm.toEquiv.nontrivial

theorem IsIrreducible.finrank_pos [FiniteDimensional k V]
    {ρ : Representation k G V} (h : ρ.IsIrreducible) : 0 < Module.finrank k V :=
  have := h.nontrivial
  Module.finrank_pos

theorem IsIrreducible.natCast_finrank_ne_zero [CharZero k]
    [FiniteDimensional k V] {ρ : Representation k G V} (h : ρ.IsIrreducible) :
    (Module.finrank k V : k) ≠ 0 :=
  Nat.cast_ne_zero.mpr h.finrank_pos.ne'

theorem isIrreducible_of_finrank_eq_one (ρ : Representation k G V)
    (h : Module.finrank k V = 1) : ρ.IsIrreducible := by
  have : IsSimpleModule k V := isSimpleModule_iff_finrank_eq_one.mpr h
  have : Nontrivial V := IsSimpleModule.nontrivial k V
  refine ⟨fun σ => (eq_bot_or_eq_top σ.toSubmodule).imp (fun hσ => ?_) fun hσ => ?_⟩
  · exact Subrepresentation.toSubmodule_injective (hσ.trans Subrepresentation.toSubmodule_bot.symm)
  · exact Subrepresentation.toSubmodule_injective (hσ.trans Subrepresentation.toSubmodule_top.symm)

instance isIrreducible_trivial_self : (trivial k G k).IsIrreducible :=
  isIrreducible_of_finrank_eq_one _ (Module.finrank_self k)

theorem isIrreducible_of_linearEquiv {W : Type*} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) (h : ρ.IsIrreducible) : σ.IsIrreducible := by
  have := h.nontrivial
  have : Nontrivial W := e.symm.toEquiv.nontrivial
  refine ⟨fun τ => ?_⟩

  let τ' : Subrepresentation ρ :=
    { toSubmodule := τ.toSubmodule.comap (e : V →ₗ[k] W)
      apply_mem_toSubmodule g v hv := by
        simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
        rw [he]
        exact τ.apply_mem_toSubmodule g hv }
  have hmap : (τ'.toSubmodule).map (e : V →ₗ[k] W) = τ.toSubmodule :=
    Submodule.map_comap_eq_of_surjective e.surjective _
  refine (eq_bot_or_eq_top τ').imp (fun hτ => ?_) fun hτ => ?_
  · refine Subrepresentation.toSubmodule_injective ?_
    rw [← hmap, hτ, Subrepresentation.toSubmodule_bot, Submodule.map_bot,
      Subrepresentation.toSubmodule_bot]
  · refine Subrepresentation.toSubmodule_injective ?_
    rw [← hmap, hτ, Subrepresentation.toSubmodule_top, Submodule.map_top, LinearEquiv.range,
      Subrepresentation.toSubmodule_top]

end Representation
