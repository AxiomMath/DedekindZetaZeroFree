module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree.KPResolventPencil

noncomputable section

def GenuineInverse {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : H →ₗ.[ℂ] H) (z : ℂ) (R : H →L[ℂ] H) : Prop :=
  ∃ hR : ∀ x : H, R x ∈ D.domain,
    (∀ x : H, D ⟨R x, hR x⟩ - z • R x = x) ∧
    (∀ y : D.domain, R (D y - z • (y : H)) = (y : H))

def shiftedPencil {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  1 - (z + 1) • B

def resolventSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | ∃ R : H →L[ℂ] H, GenuineInverse D z R}

def shiftedResolvent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  B * Ring.inverse (shiftedPencil B z)

section Algebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private lemma base_left (D : H →ₗ.[ℂ] H) (B : H →L[ℂ] H)
    (hB : GenuineInverse D (-1) B) :
    ∃ h : ∀ x : H, B x ∈ D.domain,
      (∀ x, D ⟨B x, h x⟩ = x - B x) ∧
      (∀ y : D.domain, B (D y + (y : H)) = (y : H)) := by
  rcases hB with ⟨h, h1, h2⟩
  refine ⟨h, ?_, ?_⟩
  · intro x
    have hx := h1 x
    simp only [neg_smul, one_smul, sub_neg_eq_add] at hx
    exact eq_sub_of_add_eq hx
  · simpa only [neg_smul, one_smul, sub_neg_eq_add] using h2

private lemma genuine_formula (D : H →ₗ.[ℂ] H) (B : H →L[ℂ] H)
    (hB : GenuineInverse D (-1) B) (z : ℂ)
    (hz : IsUnit (shiftedPencil B z)) :
    GenuineInverse D z (shiftedResolvent B z) := by
  rcases base_left D B hB with ⟨h, h1, h2⟩
  let A := shiftedPencil B z
  let C := Ring.inverse A
  have hAC : A * C = 1 := Ring.mul_inverse_cancel A hz
  have hCA : C * A = 1 := Ring.inverse_mul_cancel A hz
  have hAB : A * B = B * A := by
    dsimp [A, shiftedPencil]
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  have hCB : C * B = B * C := by
    calc
      C * B = C * B * (A * C) := by rw [hAC, mul_one]
      _ = C * (B * A) * C := by simp only [mul_assoc]
      _ = C * (A * B) * C := by rw [hAB]
      _ = B * C := by rw [← mul_assoc, hCA, one_mul]
  change GenuineInverse D z (B * C)
  refine ⟨fun x => h (C x), ?_, ?_⟩
  · intro x
    change D ⟨B (C x), h (C x)⟩ - z • B (C x) = x
    rw [h1]
    have he := DFunLike.congr_fun hAC x
    simp only [mul_apply_eq_comp, one_apply_eq_self,
      A, shiftedPencil, sub_apply, smul_apply] at he
    calc
      C x - B (C x) - z • B (C x) = C x - (z + 1) • B (C x) := by module
      _ = x := he
  · intro y
    have he : B (D y - z • (y : H)) = A (y : H) := by
      have hb := h2 y
      simp only [map_add] at hb
      have hd : B (D y) = (y : H) - B (y : H) := eq_sub_of_add_eq hb
      simp only [map_sub, map_smul, A, shiftedPencil, sub_apply,
        one_apply_eq_self, smul_apply]
      rw [hd]
      first | module
    rw [hCB.symm]
    simp only [mul_apply_eq_comp]
    rw [he]
    exact DFunLike.congr_fun hCA (y : H)

private lemma genuine_unit (D : H →ₗ.[ℂ] H) (B : H →L[ℂ] H)
    (hB : GenuineInverse D (-1) B) (z : ℂ) (R : H →L[ℂ] H)
    (hR : GenuineInverse D z R) : IsUnit (shiftedPencil B z) := by
  rcases base_left D B hB with ⟨h, h1, h2⟩
  rcases hR with ⟨hr, hr1, hr2⟩
  have hAR : shiftedPencil B z * R = B := by
    ext x
    have hb := h2 ⟨R x, hr x⟩
    have hd : D ⟨R x, hr x⟩ = x + z • R x := eq_add_of_sub_eq (hr1 x)
    rw [hd] at hb
    simp only [map_add, map_smul] at hb
    simp only [mul_apply_eq_comp, shiftedPencil, sub_apply,
      one_apply_eq_self, smul_apply]
    calc
      R x - (z + 1) • B (R x) = R x - (z • B (R x) + B (R x)) := by module
      _ = B x := by rw [sub_eq_iff_eq_add]; simpa only [add_assoc] using hb.symm
  have hRA : R * shiftedPencil B z = B := by
    ext x
    have hrb := hr2 ⟨B x, h x⟩
    rw [h1] at hrb
    simp only [mul_apply_eq_comp, shiftedPencil, sub_apply,
      one_apply_eq_self, smul_apply]
    have he : x - (z + 1) • B x = x - B x - z • B x := by module
    rw [he]
    exact hrb
  apply isUnit_iff_exists.mpr
  refine ⟨1 + (z + 1) • R, ?_, ?_⟩
  · rw [mul_add, mul_one, mul_smul_comm, hAR]
    simp [shiftedPencil]
  · rw [add_mul, one_mul, smul_mul_assoc, hRA]
    simp [shiftedPencil]

private lemma genuine_unique (D : H →ₗ.[ℂ] H) (z : ℂ)
    (R S : H →L[ℂ] H) (hR : GenuineInverse D z R) (hS : GenuineInverse D z S) :
    R = S := by
  rcases hR with ⟨hr, hr1, hr2⟩
  rcases hS with ⟨hs, hs1, hs2⟩
  ext x
  have he := hr2 ⟨S x, hs x⟩
  rw [hs1] at he
  exact he

end Algebra

theorem isUnit_shiftedPencil_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : H →ₗ.[ℂ] H) (hDense : Dense (D.domain : Set H))
    (B : H →L[ℂ] H) (hB : GenuineInverse D (-1) B) (z : ℂ) :
    IsUnit (shiftedPencil B z) ↔ z ∈ resolventSet D := by
  constructor
  · intro hz
    exact ⟨shiftedResolvent B z, genuine_formula D B hB z hz⟩
  · rintro ⟨R, hR⟩
    exact genuine_unit D B hB z R hR

theorem shiftedResolvent_genuine_unique
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : H →ₗ.[ℂ] H) (hDense : Dense (D.domain : Set H))
    (B : H →L[ℂ] H) (hB : GenuineInverse D (-1) B)
    (z : ℂ) (hz : IsUnit (shiftedPencil B z)) :
    GenuineInverse D z (shiftedResolvent B z) ∧
      ∀ R : H →L[ℂ] H, GenuineInverse D z R → R = shiftedResolvent B z := by
  have hg := genuine_formula D B hB z hz
  exact ⟨hg, fun R hR => genuine_unique D z R (shiftedResolvent B z) hR hg⟩

@[simp] theorem shiftedPencil_neg_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : H →L[ℂ] H) : shiftedPencil B (-1) = 1 := by
  simp [shiftedPencil]

@[simp] theorem shiftedResolvent_neg_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : H →L[ℂ] H) : shiftedResolvent B (-1) = B := by
  simp [shiftedResolvent]

theorem analyticOnNhd_shiftedResolvent
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : H →ₗ.[ℂ] H) (hDense : Dense (D.domain : Set H))
    (B : H →L[ℂ] H) (hB : GenuineInverse D (-1) B) :
    AnalyticOnNhd ℂ (shiftedResolvent B) (resolventSet D) := by
  intro z hz
  have hA : AnalyticAt ℂ (shiftedPencil B) z := by
    unfold shiftedPencil
    exact analyticAt_const.sub ((analyticAt_id.add analyticAt_const).smul analyticAt_const)
  have hi : AnalyticAt ℂ Ring.inverse (shiftedPencil B z) :=
    analyticOnNhd_inverse (𝕜 := ℂ) (shiftedPencil B z)
      ((isUnit_shiftedPencil_iff D hDense B hB z).mpr hz)
  exact analyticAt_const.mul (hi.comp hA)

end
end DedekindZetaZeroFree.KPResolventPencil
