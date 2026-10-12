module

public import Mathlib.RepresentationTheory.Irreducible

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RepresentationTheory/Subrepresentation.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

namespace Subrepresentation

variable {A G W : Type*} [Semiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W}

@[simp]
lemma mem_toSubmodule {ρ' : Subrepresentation ρ} {v : W} : v ∈ ρ'.toSubmodule ↔ v ∈ ρ' := Iff.rfl

@[simp]
lemma toSubmodule_bot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

@[simp]
lemma toSubmodule_top : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl

instance instNontrivial [Nontrivial W] : Nontrivial (Subrepresentation ρ) :=
  ⟨⟨⊥, ⊤, fun hc => _root_.bot_ne_top (α := Submodule A W) (by
    rw [← toSubmodule_bot (ρ := ρ), ← toSubmodule_top (ρ := ρ), hc])⟩⟩

@[simp]
lemma toSubmodule_le_toSubmodule {ρ₁ ρ₂ : Subrepresentation ρ} :
    ρ₁.toSubmodule ≤ ρ₂.toSubmodule ↔ ρ₁ ≤ ρ₂ := Iff.rfl

@[simp]
lemma toSubmodule_lt_toSubmodule {ρ₁ ρ₂ : Subrepresentation ρ} :
    ρ₁.toSubmodule < ρ₂.toSubmodule ↔ ρ₁ < ρ₂ := by
  simp only [lt_iff_le_not_ge, toSubmodule_le_toSubmodule]

@[simp]
theorem isCompl_toSubmodule {ρ₁ ρ₂ : Subrepresentation ρ} :
    IsCompl ρ₁.toSubmodule ρ₂.toSubmodule ↔ IsCompl ρ₁ ρ₂ := by
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff, ← toSubmodule_inf, ← toSubmodule_sup,
    ← toSubmodule_bot (ρ := ρ), ← toSubmodule_top (ρ := ρ), toSubmodule_injective.eq_iff]

theorem toRepresentation_apply (S : Subrepresentation ρ) (g : G) :
    S.toRepresentation g = (ρ g).restrict (S.apply_mem_toSubmodule g) :=
  rfl

@[simp]
theorem coe_toRepresentation_asAlgebraHom_apply {k H V : Type*} [CommSemiring k] [Monoid H]
    [AddCommMonoid V] [Module k V] {σ : Representation k H V} (S : Subrepresentation σ)
    (a : MonoidAlgebra k H) (x : S.toSubmodule) :
    ((S.toRepresentation.asAlgebraHom a x : S.toSubmodule) : V) =
      σ.asAlgebraHom a (x : V) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simpa only [map_add, LinearMap.add_apply, Submodule.coe_add] using
        congrArg₂ (fun u v => u + v) ha hb
  | single g r =>
      simp only [Representation.asAlgebraHom_single]
      congr 1

section AsSubmodule

open scoped MonoidAlgebra

variable {A G W : Type*} [CommRing A] [Monoid G] [AddCommGroup W] [Module A W]
  {ρ : Representation A G W}

@[simp]
theorem isSimpleModule_asSubmodule_iff {σ : Subrepresentation ρ} :
    IsSimpleModule A[G] σ.asSubmodule ↔ IsAtom σ :=
  isSimpleModule_iff_isAtom.trans (subrepresentationSubmoduleOrderIso.isAtom_iff σ)

end AsSubmodule

section Splitting

variable {A G W : Type*} [Ring A] [Monoid G] [AddCommGroup W] [Module A W]
  {ρ : Representation A G W}

noncomputable def equivProdOfIsCompl {ρ₁ ρ₂ : Subrepresentation ρ} (h : IsCompl ρ₁ ρ₂) :
    ρ.Equiv (ρ₁.toRepresentation.prod ρ₂.toRepresentation) :=
  (Representation.Equiv.mk
    (Submodule.prodEquivOfIsCompl ρ₁.toSubmodule ρ₂.toSubmodule (isCompl_toSubmodule.mpr h))
    fun g => LinearMap.ext fun v => by
      simp [toRepresentation_apply]).symm

@[simp]
theorem equivProdOfIsCompl_apply {ρ₁ ρ₂ : Subrepresentation ρ} (h : IsCompl ρ₁ ρ₂) (v : W) :
    equivProdOfIsCompl h v =
      (Submodule.prodEquivOfIsCompl ρ₁.toSubmodule ρ₂.toSubmodule
        (isCompl_toSubmodule.mpr h)).symm v :=

  (rfl)

@[simp]
theorem equivProdOfIsCompl_symm_apply {ρ₁ ρ₂ : Subrepresentation ρ} (h : IsCompl ρ₁ ρ₂)
    (v : ρ₁.toSubmodule × ρ₂.toSubmodule) :
    (equivProdOfIsCompl h).symm v = (v.1 : W) + (v.2 : W) :=

  (rfl)

end Splitting

end Subrepresentation

namespace MonoidHom

variable {k : Type*} [Semiring k] {H K : Type*} [Monoid H] [Monoid K]
  {V : Type*} [AddCommMonoid V] [Module k V]

def resSubrepresentationOrderIso (f : H →* K) (hf : Function.Surjective f)
    (ρ : Representation k K V) :
    Subrepresentation (ρ.comp f) ≃o Subrepresentation ρ where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun h v hv ↦ by
        obtain ⟨g, rfl⟩ := hf h
        exact S.apply_mem_toSubmodule g hv }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun h v hv ↦ S.apply_mem_toSubmodule (f h) hv }
  left_inv S := by ext; rfl
  right_inv S := by ext; rfl
  map_rel_iff' := by rfl

@[simp]
theorem resSubrepresentationOrderIso_apply_toSubmodule (f : H →* K) (hf : Function.Surjective f)
    (ρ : Representation k K V) (S : Subrepresentation (ρ.comp f)) :
    (MonoidHom.resSubrepresentationOrderIso f hf ρ S).toSubmodule = S.toSubmodule :=
  (rfl)

@[simp]
theorem resSubrepresentationOrderIso_symm_apply_toSubmodule (f : H →* K)
    (hf : Function.Surjective f) (ρ : Representation k K V) (S : Subrepresentation ρ) :
    ((MonoidHom.resSubrepresentationOrderIso f hf ρ).symm S).toSubmodule = S.toSubmodule :=
  (rfl)

end MonoidHom

section Irreducible

variable {k : Type*} [Field k] {H K : Type*} [Monoid H] [Monoid K]
  {V : Type*} [AddCommGroup V] [Module k V]

@[simp]
theorem MonoidHom.isIrreducible_comp_surjective_iff (f : H →* K) (hf : Function.Surjective f)
    (ρ : Representation k K V) :
    Representation.IsIrreducible (ρ.comp f) ↔ Representation.IsIrreducible ρ :=
  (f.resSubrepresentationOrderIso hf ρ).isSimpleOrder_iff

@[simp]
theorem MulEquiv.isIrreducible_comp_equiv_iff (e : H ≃* K) (ρ : Representation k K V) :
    Representation.IsIrreducible (ρ.comp (e : H →* K)) ↔ Representation.IsIrreducible ρ :=
  e.toMonoidHom.isIrreducible_comp_surjective_iff e.surjective ρ

end Irreducible
