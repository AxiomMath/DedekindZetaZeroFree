module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RepresentationTheory.Character
public import DedekindZetaZeroFree.RepresentationTheory.Subrepresentations.Restriction

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/FDRep.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

universe u v w

namespace Representation

@[simp]
theorem char_trivial {k : Type u} {G : Type v} {V : Type w} [Field k] [Monoid G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (g : G) :
    (trivial k G V).character g = Module.finrank k V := by
  have hone : trivial k G V g = 1 :=
    LinearMap.ext fun v => by rw [trivial_apply, Module.End.one_apply]
  rw [character, hone, LinearMap.trace_one]

@[simp]
theorem char_prod {k : Type u} {G : Type v} {V W : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W) (g : G) :
    (ρ.prod σ).character g = ρ.character g + σ.character g := by
  have hg : (ρ.prod σ) g = LinearMap.prodMap (ρ g) (σ g) := rfl
  rw [character, character, character, hg]
  exact LinearMap.trace_prodMap' (ρ g) (σ g)

end Representation

namespace Subrepresentation

@[simp]
theorem char_add_eq_of_isCompl {k : Type u} {G : Type v} {V : Type w} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] {ρ : Representation k G V}
    {ρ₁ ρ₂ : Subrepresentation ρ} (h : IsCompl ρ₁ ρ₂) :
    ρ₁.toRepresentation.character + ρ₂.toRepresentation.character = ρ.character := by
  funext g
  rw [Pi.add_apply, ← Representation.char_prod, Representation.char_iso (equivProdOfIsCompl h)]

end Subrepresentation

namespace FDRep

open CategoryTheory

instance (priority := 100) forget₂Rep {R : Type u} [Ring R] {G : Type v} [Monoid G] :
    HasForget₂ (FDRep R G) (Rep R G) where
  forget₂ := (forget₂ (FGModuleCat R) (ModuleCat R)).mapAction G ⋙ Rep.ActionToRep R G

@[simp]
theorem character_of_trivial {k : Type u} {G : Type v} [Field k] [Monoid G] (g : G) :
    (FDRep.of (Representation.trivial k G k)).character g = 1 := by
  rw [FDRep.character, FDRep.of_ρ']

  exact (Representation.char_trivial g).trans (by simp)

@[simp]
theorem character_actionRes {k : Type u} {G : Type v} {H : Type w} [Field k] [Monoid G]
    [Monoid H] (V : FDRep k G) (phi : H →* G) (h : H) :
    FDRep.character ((Action.res (FGModuleCat k) phi).obj V) h = V.character (phi h) :=
  (rfl)

instance moduleFinite_forget₂_obj {R : Type u} {G : Type v} [Ring R] [Monoid G]
    (A : FDRep R G) : Module.Finite R ((forget₂ (FDRep R G) (Rep R G)).obj A) :=
  inferInstanceAs (Module.Finite R A.V)

@[simp]
theorem finrank_forget₂_obj {R : Type u} {G : Type v} [CommRing R] [Monoid G]
    (A : FDRep R G) :
    Module.finrank R ((forget₂ (FDRep R G) (Rep R G)).obj A) = Module.finrank R A :=
  rfl

@[simp]
theorem character_forget₂_obj {k : Type u} {G : Type v} [Field k] [Monoid G] (A : FDRep k G)
    (g : G) : ((forget₂ (FDRep k G) (Rep k G)).obj A).ρ.character g = A.character g := by
  rw [FDRep.character, Representation.character, FDRep.forget₂_ρ]

  rfl

@[simp]
theorem character_ρ {k : Type u} {G : Type v} [Field k] [Monoid G] (A : FDRep k G) (g : G) :
    Representation.character A.ρ g = A.character g :=
  rfl

@[simp]
theorem character_of {k : Type u} {G : Type v} {V : Type u} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (rho : Representation k G V) :
    (FDRep.of rho).character = rho.character :=
  rfl

@[simp]
theorem of_ρ_eq_self {R : Type u} {G : Type v} [CommRing R] [Monoid G] (A : FDRep R G) :
    FDRep.of A.ρ = A := (rfl)

instance forget₂_additive {R : Type u} {G : Type v} [CommRing R] [Monoid G] :
    (forget₂ (FDRep R G) (Rep R G)).Additive where
  map_add := by
    intros
    apply Rep.hom_ext
    ext x

    rfl

section Biproduct

open CategoryTheory Limits

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

private theorem trace_comp_of_retraction {X B : FDRep k G} (i : X ⟶ B) (p : B ⟶ X)
    (h : i ≫ p = 𝟙 X) (g : G) :
    LinearMap.trace k B ((B.ρ g ∘ₗ i.hom.hom.hom) ∘ₗ p.hom.hom.hom) = X.character g := by

  have hcomm : i.hom.hom.hom ∘ₗ X.ρ g = B.ρ g ∘ₗ i.hom.hom.hom := by
    simpa using congrArg (fun t : X.V ⟶ B.V => t.hom.hom) (i.comm g)

  have hpi : p.hom.hom.hom ∘ₗ i.hom.hom.hom = LinearMap.id := by
    simpa using congrArg (fun t : X ⟶ X => t.hom.hom.hom) h
  rw [LinearMap.trace_comp_comm', ← hcomm, ← LinearMap.comp_assoc, hpi]
  simp [FDRep.character]

@[simp]
theorem char_biprod (X Y : FDRep k G) : (X ⊞ Y).character = X.character + Y.character := by
  ext g
  have htot : (biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom ∘ₗ (biprod.fst : X ⊞ Y ⟶ X).hom.hom.hom
      + (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom ∘ₗ (biprod.snd : X ⊞ Y ⟶ Y).hom.hom.hom
      = LinearMap.id := by
    have h := congrArg (fun t : (X ⊞ Y) ⟶ (X ⊞ Y) => t.hom.hom.hom)
      (biprod.total (X := X) (Y := Y))
    simp only [Action.id_hom] at h
    exact h
  have hsplit : (X ⊞ Y).ρ g
      = ((X ⊞ Y).ρ g ∘ₗ (biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom)
          ∘ₗ (biprod.fst : X ⊞ Y ⟶ X).hom.hom.hom
        + ((X ⊞ Y).ρ g ∘ₗ (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom)
          ∘ₗ (biprod.snd : X ⊞ Y ⟶ Y).hom.hom.hom := by
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← LinearMap.comp_add, htot,
      LinearMap.comp_id]
  rw [FDRep.character, hsplit, map_add,
    trace_comp_of_retraction biprod.inl biprod.fst biprod.inl_fst,
    trace_comp_of_retraction biprod.inr biprod.snd biprod.inr_snd, Pi.add_apply]

end Biproduct

section TensorUnit

open CategoryTheory MonoidalCategory

@[simp]
theorem char_tensorUnit (k : Type u) (G : Type v) [Field k] [Monoid G] :
    (𝟙_ (FDRep k G)).character = 1 := by
  ext g

  have hunit : 𝟙_ (FDRep k G) = FDRep.of (Representation.trivial k G k) := rfl
  rw [hunit, Pi.one_apply, character_of_trivial]

end TensorUnit

section Kernel

variable {k : Type u} {G : Type v} [Field k] [Group G]

@[simp]
theorem char_mul_of_mem_ker_left (V : FDRep k G) {g : G} (hg : g ∈ V.ρ.ker) (h : G) :
    V.character (g * h) = V.character h := by
  simp only [character, map_mul, MonoidHom.mem_ker.1 hg, one_mul]

end Kernel

section CommonKernel

variable {ι : Type*} {k : Type u} {G : Type v} [CommRing k] [Group G]

instance normal_iInf_ker (W : ι → FDRep k G) : (⨅ i, (W i).ρ.ker).Normal :=
  Subgroup.normal_iInf_normal fun _ => inferInstance

end CommonKernel

end FDRep
