module

public import DedekindZetaZeroFree.Algebra.Groups.NormalizerQuotient
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.MaximalTorus

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/SU2/Weyl/Basic.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

namespace DedekindZetaZeroFree.TauCeti

namespace SU2

def weylMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

theorem weylMatrix_mem : weylMatrix ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [weylMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
  · simp [weylMatrix, Matrix.det_fin_two]

def weylElement : SU2 := ⟨weylMatrix, weylMatrix_mem⟩

@[simp]
theorem coe_weylElement : (weylElement : Matrix (Fin 2) (Fin 2) ℂ) = weylMatrix := (rfl)

theorem weylElement_notMem_torus : weylElement ∉ torus := by
  intro hmem
  have h01 : (weylElement : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := mem_torus_iff.mp hmem (by decide)
  rw [coe_weylElement] at h01
  simp [weylMatrix] at h01

theorem weylMatrix_mul_torusMatrix (z : Circle) :
    weylMatrix * torusMatrix z = torusMatrix z⁻¹ * weylMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem weylElement_mul_torusHom (z : Circle) :
    weylElement * torusHom z = torusHom z⁻¹ * weylElement := by
  refine Subtype.ext ?_
  simp only [Submonoid.coe_mul, coe_weylElement, coe_torusHom]
  exact weylMatrix_mul_torusMatrix z

@[simp]
theorem weylElement_conj_torusHom (z : Circle) :
    weylElement * torusHom z * weylElement⁻¹ = torusHom z⁻¹ :=
  mul_inv_eq_iff_eq_mul.mpr (weylElement_mul_torusHom z)

theorem weylElement_mem_normalizer :
    weylElement ∈ Subgroup.normalizer (torus : Set SU2) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨z, rfl⟩ := mem_torus_iff_exists_torusHom.mp hh
    rw [weylElement_conj_torusHom]
    exact torusHom_mem_torus z⁻¹
  · intro hh
    obtain ⟨u, hu⟩ := mem_torus_iff_exists_torusHom.mp hh
    have hcancel : weylElement * torusHom u⁻¹ * weylElement⁻¹
        = weylElement * h * weylElement⁻¹ := by
      rw [weylElement_conj_torusHom, inv_inv, hu]
    rw [← mul_left_cancel (mul_right_cancel hcancel)]
    exact torusHom_mem_torus u⁻¹

theorem mem_normalizer_torus_iff {g : SU2} :
    g ∈ Subgroup.normalizer (torus : Set SU2) ↔ g ∈ torus ∨ weylElement⁻¹ * g ∈ torus := by

  obtain ⟨z, hz⟩ := exists_centralizer_torusHom_eq_torus
  have hdetect : ∀ h : SU2, torusHom z * h = h * torusHom z → h ∈ torus := fun h hh => by
    rw [← hz, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact hh
  constructor
  · intro hg
    obtain ⟨u, hu⟩ := mem_torus_iff_exists_torusHom.mp
      ((Subgroup.mem_normalizer_iff.mp hg (torusHom z)).mp (torusHom_mem_torus z))
    rcases eq_or_eq_inv_of_conj_torusHom hu.symm with rfl | rfl
    · refine Or.inl (hdetect _ ?_)
      conv_lhs => rw [hu]
      group
    · refine Or.inr (hdetect _ ?_)
      have hconj : weylElement * torusHom z * weylElement⁻¹
          = g * torusHom z * g⁻¹ := by rw [weylElement_conj_torusHom, hu]
      calc torusHom z * (weylElement⁻¹ * g)
          = weylElement⁻¹ * (weylElement * torusHom z * weylElement⁻¹) * g := by group
        _ = weylElement⁻¹ * (g * torusHom z * g⁻¹) * g := by rw [hconj]
        _ = weylElement⁻¹ * g * torusHom z := by group
  · rintro (hg | hg)
    · exact Subgroup.le_normalizer hg
    · have hgeq : g = weylElement * (weylElement⁻¹ * g) := by group
      rw [hgeq]
      exact mul_mem weylElement_mem_normalizer (Subgroup.le_normalizer hg)

abbrev weylGroup : Type := Subgroup.normalizerQuotient torus

noncomputable def weylNormalizerElement : ↥(Subgroup.normalizer (torus : Set SU2)) :=
  ⟨weylElement, weylElement_mem_normalizer⟩

@[simp]
theorem coe_weylNormalizerElement : (weylNormalizerElement : SU2) = weylElement := (rfl)

noncomputable def weylClass : weylGroup :=
  Subgroup.normalizerQuotientMk torus weylNormalizerElement

theorem weylClass_ne_one : weylClass ≠ 1 := fun h =>
  weylElement_notMem_torus
    ((Subgroup.normalizerQuotientMk_eq_one_iff torus weylNormalizerElement).mp h)

@[simp]
theorem weylClass_sq : weylClass ^ 2 = 1 := by
  rw [weylClass, ← map_pow]
  refine (Subgroup.normalizerQuotientMk_eq_one_iff torus _).mpr ?_
  have hcoe : ((weylNormalizerElement ^ 2 : ↥(Subgroup.normalizer (torus : Set SU2))) : SU2)
      = weylElement * weylElement := by
    rw [SubmonoidClass.coe_pow, coe_weylNormalizerElement, sq]
  rw [hcoe]
  refine mem_torus_iff.mpr fun i j hij => ?_
  fin_cases i <;> fin_cases j <;>
    simp_all [weylMatrix, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem weylClass_inv : weylClass⁻¹ = weylClass :=
  inv_eq_of_mul_eq_one_right (by rw [← sq, weylClass_sq])

theorem eq_one_or_eq_weylClass (q : weylGroup) : q = 1 ∨ q = weylClass := by
  obtain ⟨n, rfl⟩ := Subgroup.normalizerQuotientMk_surjective torus q
  rcases mem_normalizer_torus_iff.mp n.2 with h | h
  · exact Or.inl ((Subgroup.normalizerQuotientMk_eq_one_iff torus n).mpr h)
  · refine Or.inr ?_
    have hq : Subgroup.normalizerQuotientMk torus (weylNormalizerElement⁻¹ * n) = 1 :=
      (Subgroup.normalizerQuotientMk_eq_one_iff torus _).mpr (by simpa using h)
    rw [map_mul, map_inv, inv_mul_eq_one] at hq
    exact hq.symm

theorem card_weylGroup : Nat.card weylGroup = 2 := by
  refine Nat.card_eq_two_iff.mpr ⟨1, weylClass, weylClass_ne_one.symm, ?_⟩
  refine Set.eq_univ_iff_forall.mpr fun q => ?_
  rcases eq_one_or_eq_weylClass q with rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl

instance instFiniteWeylGroup : Finite weylGroup :=
  Nat.finite_of_card_ne_zero (by rw [card_weylGroup]; norm_num)

end SU2

end DedekindZetaZeroFree.TauCeti
