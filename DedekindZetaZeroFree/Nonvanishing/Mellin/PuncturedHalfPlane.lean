module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.HalfPlane

@[expose] public section

namespace DedekindZetaZeroFree

theorem mellin_punctured_halfplane_isOpen (σ : ℝ) (hσ : σ < 1) :
    IsOpen {s : ℂ | σ < s.re ∧ s ≠ 1} := by
  exact (Complex.isOpen_re_gt σ).inter isOpen_ne

theorem mellin_punctured_halfplane_isPreconnected (σ : ℝ) (hσ : σ < 1) :
    IsPreconnected {s : ℂ | σ < s.re ∧ s ≠ 1} := by
  let R : Set ℂ := {s | 1 < s.re}
  let U : Set ℂ := {s | σ < s.re} ∩ {s | 0 < s.im}
  let D : Set ℂ := {s | σ < s.re} ∩ {s | s.im < 0}
  let L : Set ℂ := {s | σ < s.re} ∩ {s | s.re < 1}
  have hR : IsPreconnected R := (convex_halfSpace_re_gt 1).isPreconnected
  have hU : IsPreconnected U := ((convex_halfSpace_re_gt σ).inter
    (convex_halfSpace_im_gt 0)).isPreconnected
  have hD : IsPreconnected D := ((convex_halfSpace_re_gt σ).inter
    (convex_halfSpace_im_lt 0)).isPreconnected
  have hL : IsPreconnected L := ((convex_halfSpace_re_gt σ).inter
    (convex_halfSpace_re_lt 1)).isPreconnected
  have hRU : IsPreconnected (R ∪ U) := hR.union (2 + Complex.I)
    (by simp [R]) (by simp [U]; linarith) hU
  have hRUD : IsPreconnected ((R ∪ U) ∪ D) := hRU.union (2 - Complex.I)
    (by left; simp [R]) (by simp [D]; linarith) hD
  have hAll : IsPreconnected (((R ∪ U) ∪ D) ∪ L) :=
    hRUD.union (((σ + 1) / 2 : ℝ) + Complex.I)
      (by left; right; simp [U]; linarith)
      (by simp [L]; constructor <;> linarith) hL
  have heq : (((R ∪ U) ∪ D) ∪ L) = {s : ℂ | σ < s.re ∧ s ≠ 1} := by
    ext s
    simp only [R, U, D, L, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro (((hr | hu) | hd) | hl)
      · exact ⟨lt_trans hσ hr, fun h => by simpa [h] using hr⟩
      · exact ⟨hu.1, fun h => by simpa [h] using hu.2⟩
      · exact ⟨hd.1, fun h => by simpa [h] using hd.2⟩
      · exact ⟨hl.1, fun h => by simpa [h] using hl.2⟩
    · rintro ⟨hs, hn⟩
      by_cases hr : 1 < s.re
      · exact Or.inl (Or.inl (Or.inl hr))
      by_cases hl : s.re < 1
      · exact Or.inr ⟨hs, hl⟩
      by_cases hi : 0 < s.im
      · exact Or.inl (Or.inl (Or.inr ⟨hs, hi⟩))
      by_cases hd : s.im < 0
      · exact Or.inl (Or.inr ⟨hs, hd⟩)
      exfalso
      apply hn
      apply Complex.ext <;> simp only [Complex.one_re, Complex.one_im] <;> linarith
  rwa [heq] at hAll

theorem mellin_punctured_halfplane_two_mem (σ : ℝ) (hσ : σ < 1) :
    (2 : ℂ) ∈ {s : ℂ | σ < s.re ∧ s ≠ 1} := by
  constructor
  · change σ < 2; linarith
  · norm_num

theorem mellin_punctured_halfplane_two_accPt :
    AccPt (2 : ℂ) (Filter.principal
      {s : ℂ | ∃ t : ℝ, t ≠ 0 ∧ s = (2 : ℂ) + t * Complex.I}) := by
  rw [accPt_iff_nhds]
  intro V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨(2 : ℂ) + (ε / 2 : ℝ) * Complex.I, ⟨hball ?_, ?_⟩, ?_⟩
  · simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    rw [abs_of_pos (by positivity)]
    linarith
  · exact ⟨ε / 2, by positivity, rfl⟩
  · intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith

end DedekindZetaZeroFree
