module

public import Mathlib.Analysis.Matrix.Spectrum
public import DedekindZetaZeroFree.Analysis.MatrixGroups.UnitaryScalarDecomposition
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.WeylGroup

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/SU2/TorusConjugacy.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

namespace DedekindZetaZeroFree.TauCeti

namespace SU2

private theorem isDiag_star_left_conjugate_of_eq_smul_one_add_smul {R n : Type*}
    [CommSemiring R] [Star R] [Fintype n] [DecidableEq n] {G H U : Matrix n n R} {a b : R}
    (hdecomp : G = a • (1 : Matrix n n R) + b • H)
    (hUU : star U * U = 1) (hdiagH : (star U * H * U).IsDiag) :
    (star U * G * U).IsDiag := by
  have hexpand : star U * G * U = a • (1 : Matrix n n R) + b • (star U * H * U) := by
    conv_lhs => rw [hdecomp]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [hUU]
  rw [hexpand]
  exact (Matrix.isDiag_one.smul _).add (hdiagH.smul _)

private theorem coe_eq_smul_one_add_smul_I_smul_sub_star (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ)
      = (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + (-Complex.I / 2) •
          (Complex.I • ((g : Matrix (Fin 2) (Fin 2) ℂ) - star (g : Matrix (Fin 2) (Fin 2) ℂ))) := by
  have hscalar : (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) / 2) •
      (1 : Matrix (Fin 2) (Fin 2) ℂ)
      = (2⁻¹ : ℂ) • ((g : Matrix (Fin 2) (Fin 2) ℂ) + star (g : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [coe_add_star g, smul_smul]
    congr 1
    ring
  have hI : (-Complex.I / 2) * Complex.I = 2⁻¹ := by
    rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]
    norm_num
  rw [smul_smul, hI, hscalar]
  module

private theorem exists_conj_mem_torus_of_isDiag_star_left_conjugate (g : SU2)
    {U : Matrix.unitaryGroup (Fin 2) ℂ}
    (hdiagG : (star (U : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)
      * (U : Matrix (Fin 2) (Fin 2) ℂ)).IsDiag) :
    ∃ u : SU2, u * g * u⁻¹ ∈ torus := by
  obtain ⟨c, hc⟩ := Matrix.exists_circle_smul_mem_specialUnitaryGroup U
  obtain ⟨u, hu⟩ : ∃ u : SU2,
    (u : Matrix (Fin 2) (Fin 2) ℂ) = (c : ℂ) • (U : Matrix (Fin 2) (Fin 2) ℂ) := ⟨⟨_, hc⟩, rfl⟩
  refine ⟨u⁻¹, mem_torus_iff.mpr ?_⟩

  have hcoe : ((u⁻¹ * g * (u⁻¹)⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
      = star (u : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)
        * (u : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [inv_inv, Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.star_eq_inv,
      Matrix.specialUnitaryGroup.coe_star]
  have hcmul : (c : ℂ) * star (c : ℂ) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  rw [hcoe, hu]
  simp only [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcmul, one_smul]
  exact hdiagG

theorem exists_conj_mem_torus (g : SU2) : ∃ u : SU2, u * g * u⁻¹ ∈ torus := by
  set G : Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ)
  set H : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • (G - star G) with hHdef

  have hHerm : H.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSelfAdjoint, isSelfAdjoint_iff, hHdef, star_smul, star_sub,
      star_star, Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]

  obtain ⟨U, hdiagH⟩ : ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
      (star (U : Matrix (Fin 2) (Fin 2) ℂ) * H * (U : Matrix (Fin 2) (Fin 2) ℂ)).IsDiag := by
    refine ⟨hHerm.eigenvectorUnitary, ?_⟩
    have h := hHerm.conjStarAlgAut_star_eigenvectorUnitary (𝕜 := ℂ)
    rw [Unitary.conjStarAlgAut_star_apply] at h
    rw [h]
    exact Matrix.isDiag_diagonal _

  exact exists_conj_mem_torus_of_isDiag_star_left_conjugate g
    (isDiag_star_left_conjugate_of_eq_smul_one_add_smul
      (coe_eq_smul_one_add_smul_I_smul_sub_star g) (Matrix.UnitaryGroup.star_mul_self U) hdiagH)

theorem exists_isConj_torusHom (g : SU2) : ∃ z : Circle, IsConj g (torusHom z) := by
  obtain ⟨u, hu⟩ := exists_conj_mem_torus g
  obtain ⟨z, hz⟩ := mem_torus_iff_exists_torusHom.mp hu
  exact ⟨z, isConj_iff.mpr ⟨u, hz.symm⟩⟩

theorem exists_isConj_torusExp (g : SU2) : ∃ θ : ℝ, IsConj g (torusExp θ) := by
  obtain ⟨z, hz⟩ := exists_isConj_torusHom g
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective z
  exact ⟨θ, by rwa [torusExp_def]⟩

theorem isConj_inv_of_mem_torus {g : SU2} (hg : g ∈ torus) : IsConj g g⁻¹ := by
  obtain ⟨z, rfl⟩ := mem_torus_iff_exists_torusHom.mp hg
  exact isConj_iff.mpr ⟨weylElement, by rw [weylElement_conj_torusHom, map_inv]⟩

theorem isConj_torusHom_iff {z w : Circle} :
    IsConj (torusHom z) (torusHom w) ↔ w = z ∨ w = z⁻¹ := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := isConj_iff.mp h
    exact eq_or_eq_inv_of_conj_torusHom hu
  · rintro (rfl | rfl)
    · exact IsConj.refl _
    · rw [map_inv]
      exact isConj_inv_of_mem_torus (torusHom_mem_torus z)

theorem eq_of_conjInvariant_of_eqOn_torus {α : Type*} {f₁ f₂ : SU2 → α}
    (h₁ : ∀ u g : SU2, f₁ (u * g * u⁻¹) = f₁ g) (h₂ : ∀ u g : SU2, f₂ (u * g * u⁻¹) = f₂ g)
    (h : Set.EqOn f₁ f₂ (torus : Set SU2)) : f₁ = f₂ := by
  funext g
  obtain ⟨u, hu⟩ := exists_conj_mem_torus g
  rw [← h₁ u g, ← h₂ u g]
  exact h hu

end SU2

end DedekindZetaZeroFree.TauCeti
