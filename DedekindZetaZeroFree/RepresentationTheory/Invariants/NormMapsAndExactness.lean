module

public import Mathlib.RepresentationTheory.Rep.Iso
public import DedekindZetaZeroFree.RepresentationTheory.Irreducible.SubrepresentationsAndEigenvectors
public import DedekindZetaZeroFree.RepresentationTheory.GroupAlgebra.AssociatedModules
public import DedekindZetaZeroFree.RepresentationTheory.GroupAlgebra.ModuleRepresentations
public import DedekindZetaZeroFree.RepresentationTheory.Restriction.ChangeOfGroup

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Invariants.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

variable (ρ : Representation k G V) [Fintype G] [Invertible (Fintype.card G : k)]

theorem averageMap_eq_invOf_card_smul_norm :
    ρ.averageMap = ⅟(Fintype.card G : k) • ρ.norm := by
  simp only [averageMap, GroupAlgebra.average, map_smul, map_sum, MonoidAlgebra.of_apply,
    asAlgebraHom_single_one, norm]

@[simp]
theorem range_norm_eq_invariants : LinearMap.range ρ.norm = ρ.invariants := by
  rw [← ρ.isProj_averageMap.range, averageMap_eq_invOf_card_smul_norm]
  refine le_antisymm ?_ (LinearMap.range_smul_le_range _ _)
  convert LinearMap.range_smul_le_range (⅟(Fintype.card G : k) • ρ.norm) (Fintype.card G : k)
  rw [smul_smul, mul_invOf_self, one_smul]

end Representation

namespace Representation

@[simp]
theorem range_norm_trivial (k H : Type*) [CommSemiring k] [Group H] [Fintype H] :
    LinearMap.range (Representation.trivial k H k).norm = Ideal.span {(Nat.card H : k)} := by
  ext x
  simp [Representation.norm, Ideal.mem_span_singleton', mul_comm]

end Representation

namespace Representation

open scoped MonoidAlgebra

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

section Finite

variable [Fintype G]

private theorem norm_leftRegular_single_coeff_one {x : MonoidAlgebra k G}
    (hx : x ∈ (leftRegular k G).invariants) :
    (leftRegular k G).norm (MonoidAlgebra.single 1 (x.coeff 1)) = x := by
  ext g
  have hcoeff : x.coeff g = x.coeff 1 := by
    have h := congrArg (fun z : MonoidAlgebra k G => z.coeff g) (hx g)
    simpa using h.symm
  simp [norm, hcoeff]

private theorem range_norm_free_eq_invariants (ι : Type*) :
    LinearMap.range (ofModule' (k := k) (G := G) (ι →₀ MonoidAlgebra k G)).norm =
      (ofModule' (k := k) (G := G) (ι →₀ MonoidAlgebra k G)).invariants := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact fun g => self_norm_apply _ g x
  · rintro x hx
    have hxi (i : ι) : x i ∈ (leftRegular k G).invariants := fun g => by
      have h := DFunLike.congr_fun (hx g) i
      rwa [DedekindZetaZeroFree.TauCeti.Representation.ofModule'_apply, Finsupp.smul_apply, smul_eq_mul,
        ← asAlgebraHom_ofMulAction_smul_eq_mul, asAlgebraHom_single_one] at h
    refine ⟨Finsupp.mapRange (fun a => MonoidAlgebra.single 1 (a.coeff 1)) (by simp) x, ?_⟩
    ext i : 1
    rw [← norm_leftRegular_single_coeff_one (hxi i)]
    simp only [norm, LinearMap.sum_apply, Finsupp.finsetSum_apply,
      DedekindZetaZeroFree.TauCeti.Representation.ofModule'_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, ← asAlgebraHom_ofMulAction_smul_eq_mul, asAlgebraHom_single_one]

@[simp]
theorem range_norm_eq_invariants_of_projective (ρ : Representation k G V)
    [Module.Projective k[G] ρ.asModule] :
    LinearMap.range ρ.norm = ρ.invariants := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact fun g => self_norm_apply _ g x
  · rintro x hx
    obtain ⟨s, hs⟩ := Module.projective_def.mp ‹Module.Projective k[G] ρ.asModule›
    let τ := ofModule' (k := k) (G := G) (ρ.asModule →₀ MonoidAlgebra k G)
    let E : τ.asModule ≃ₗ[k[G]] (ρ.asModule →₀ MonoidAlgebra k G) :=
      DedekindZetaZeroFree.TauCeti.Representation.ofModule'AsModuleEquiv _
    let F : IntertwiningMap τ ρ := (IntertwiningMap.equivLinearMapAsModule τ ρ).symm
      (Finsupp.linearCombination k[G] id ∘ₗ E.toLinearMap)
    let S : IntertwiningMap ρ τ :=
      (IntertwiningMap.equivLinearMapAsModule ρ τ).symm (E.symm.toLinearMap ∘ₗ s)
    have hSx : S x ∈ τ.invariants := fun g => by
      rw [← IntertwiningMap.isIntertwining ρ τ S g x, hx g]
    obtain ⟨y, hy⟩ : S x ∈ LinearMap.range τ.norm := by
      rw [range_norm_free_eq_invariants]
      exact hSx

    have hF : τ.IsIntertwiningMap (ρ.comp ((MulEquiv.refl G : G ≃* G) : G →* G))
        F.toLinearMap := ⟨IntertwiningMap.isIntertwining τ ρ F⟩
    have hN : F (τ.norm y) = ρ.norm (F y) := LinearMap.congr_fun hF.comp_norm y
    have hF_apply (z : ρ.asModule →₀ MonoidAlgebra k G) :
        F z = ρ.asModuleEquiv
          (Finsupp.linearCombination k[G] id (E (τ.asModuleEquiv.symm z))) := by
      simp only [F, IntertwiningMap.equivLinearMapAsModule_symm_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe]
    have hS_apply (z : V) :
        S z = τ.asModuleEquiv (E.symm (s (ρ.asModuleEquiv.symm z))) := by
      simp only [S, IntertwiningMap.equivLinearMapAsModule_symm_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe]

    have hFS : F (S x) = x := by
      simpa only [hF_apply, hS_apply, LinearEquiv.symm_apply_apply, E.apply_symm_apply,
        LinearEquiv.apply_symm_apply] using congrArg ρ.asModuleEquiv (hs (ρ.asModuleEquiv.symm x))
    exact ⟨F y, by rw [← hN, hy, hFS]⟩

end Finite

end Representation

namespace Representation.IsIrreducible

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

theorem invariants_eq_bot {ρ : Representation k G V} (h : ρ.IsIrreducible)
    (hρ : ρ ≠ trivial k G V) : ρ.invariants = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun v hv => by_contra fun hv0 => hρ ?_
  let f : IntertwiningMap (trivial k G k) ρ :=
    (LinearMap.toSpanSingleton k V v).intertwiningMap_of_isIntertwiningMap _ _ fun g c => by
      rw [trivial_apply, LinearMap.toSpanSingleton_apply, map_smul]
      exact congrArg (c • ·) (hv g).symm
  have hf_one : f.toLinearMap 1 = v := by
    simp [f]
  have hsurj : Function.Surjective f.toLinearMap :=
    (IsIrreducible.surjective_or_eq_zero f).resolve_right fun hf =>
      hv0 <| calc
        v = f.toLinearMap 1 := hf_one.symm
        _ = (0 : IntertwiningMap (trivial k G k) ρ).toLinearMap 1 :=
          congrArg (fun φ : IntertwiningMap (trivial k G k) ρ => φ.toLinearMap 1) hf
        _ = 0 := rfl
  ext g x
  obtain ⟨c, rfl⟩ := hsurj x
  simpa using (IntertwiningMap.isIntertwining (trivial k G k) ρ f g c).symm

theorem invariants_eq_bot_of_finrank_ne_one {ρ : Representation k G V} (h : ρ.IsIrreducible)
    (hV : Module.finrank k V ≠ 1) : ρ.invariants = ⊥ := by
  refine h.invariants_eq_bot fun hρ => hV ?_
  subst ρ
  let _ := h.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let f : IntertwiningMap (trivial k G k) (trivial k G V) :=
    (LinearMap.toSpanSingleton k V v).intertwiningMap_of_isIntertwiningMap _ _ fun g c => by
      simp only [trivial_apply, LinearMap.toSpanSingleton_apply, map_smul]
  have hsurj : Function.Surjective f.toLinearMap :=
    (IsIrreducible.surjective_or_eq_zero f).resolve_right fun hf =>
      hv <| calc
        v = f.toLinearMap 1 := by simp [f]
        _ = (0 : IntertwiningMap (trivial k G k) (trivial k G V)).toLinearMap 1 :=
          congrArg (fun φ : IntertwiningMap (trivial k G k) (trivial k G V) =>
            φ.toLinearMap 1) hf
        _ = 0 := rfl
  apply finrank_eq_one v hv
  intro w
  obtain ⟨c, hc⟩ := hsurj w
  exact ⟨c, by simpa only [f, LinearMap.intertwiningMap_of_isIntertwiningMap,
    LinearMap.toSpanSingleton_apply] using hc⟩

end Representation.IsIrreducible

namespace DedekindZetaZeroFree.TauCeti

variable {k G : Type*} [CommRing k] [Group G] (S : Subgroup G) [S.Normal]

instance : (Rep.quotientToInvariantsFunctor k S).Additive where

end DedekindZetaZeroFree.TauCeti
