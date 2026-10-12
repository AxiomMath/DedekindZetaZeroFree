module

public import DedekindZetaZeroFree.Analysis.Gamma.QuotientBounds
public import DedekindZetaZeroFree.Analysis.Gamma.ReciprocalRecurrenceAndRisingProducts

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Vendor

private lemma gamma_ne_zero_of_im_ne (z : ℂ) (hz : z.im ≠ 0) : Complex.Gamma z ≠ 0 := by
  intro h
  rw [Complex.Gamma_eq_zero_iff] at h
  obtain ⟨m, rfl⟩ := h
  simpa using hz

private lemma sqrt_pi_ne_zero : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 Real.pi_pos))

private lemma gamma_mul_half (s : ℂ) :
    Complex.Gamma (s / 2) * Complex.Gamma ((1 + s) / 2) =
      Complex.Gamma s * (2 : ℂ) ^ (1 - s) * ↑(Real.sqrt Real.pi) := by
  have h := Complex.Gamma_mul_Gamma_add_half (s / 2)
  rw [show 2 * (s / 2) = s by ring, show s / 2 + 1 / 2 = (1 + s) / 2 by ring] at h
  exact h

private lemma gamma_one_sub_mul (s : ℂ) :
    Complex.Gamma ((1 - s) / 2) * Complex.Gamma (1 - s / 2) =
      Complex.Gamma (1 - s) * (2 : ℂ) ^ s * ↑(Real.sqrt Real.pi) := by
  have h := Complex.Gamma_mul_Gamma_add_half ((1 - s) / 2)
  rw [show 2 * ((1 - s) / 2) = 1 - s by ring, show (1 - s) / 2 + 1 / 2 = 1 - s / 2 by ring] at h
  rw [show (1 : ℂ) - (1 - s) = s by ring] at h
  exact h

private lemma two_pi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

theorem reflected_square_gamma_duplication (s : ℂ) (hs : s.im ≠ 0) :
    Complex.Gammaℂ s * Complex.Gammaℂ ((1 - s) / 2) /
        (Complex.Gammaℂ (1 - s) * Complex.Gammaℂ ((1 + s) / 2)) =
      (2 : ℂ) ^ (2 * s - 1) * Complex.Gammaℂ (s / 2) /
        Complex.Gammaℂ (1 - s / 2) := by
  have hGs2 : Complex.Gamma (s / 2) ≠ 0 :=
    gamma_ne_zero_of_im_ne _ (by simp [Complex.div_im, hs])
  have hG1ps2 : Complex.Gamma ((1 + s) / 2) ≠ 0 :=
    gamma_ne_zero_of_im_ne _ (by simp [Complex.div_im, Complex.add_im, hs])
  have hG1s2 : Complex.Gamma ((1 - s) / 2) ≠ 0 :=
    gamma_ne_zero_of_im_ne _ (by simp [Complex.div_im, Complex.sub_im, hs])
  have hG1ms2 : Complex.Gamma (1 - s / 2) ≠ 0 :=
    gamma_ne_zero_of_im_ne _ (by simp [Complex.div_im, Complex.sub_im, hs])
  have hG2ms2 : Complex.Gamma ((2 - s) / 2) ≠ 0 :=
    gamma_ne_zero_of_im_ne _ (by simp [Complex.div_im, Complex.sub_im, hs])
  have hGs_eq : Complex.Gamma s = Complex.Gamma (s / 2) * Complex.Gamma ((1 + s) / 2) /
      ((2 : ℂ) ^ (1 - s) * ↑(Real.sqrt Real.pi)) := by
    rw [eq_div_iff (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)) sqrt_pi_ne_zero)]
    rw [← mul_assoc, ← gamma_mul_half s]
  have hG1s_eq : Complex.Gamma (1 - s) = Complex.Gamma ((1 - s) / 2) * Complex.Gamma (1 - s / 2) /
      ((2 : ℂ) ^ s * ↑(Real.sqrt Real.pi)) := by
    rw [eq_div_iff (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)) sqrt_pi_ne_zero)]
    rw [← mul_assoc, ← gamma_one_sub_mul s]
  rw [Complex.Gammaℂ_def, Complex.Gammaℂ_def, Complex.Gammaℂ_def, Complex.Gammaℂ_def,
    Complex.Gammaℂ_def, Complex.Gammaℂ_def]
  rw [hGs_eq, hG1s_eq]
  field_simp [two_pi_ne_zero, two_ne_zero, sqrt_pi_ne_zero, hGs2, hG1ps2, hG1s2, hG1ms2, hG2ms2,
    Complex.cpow_ne_zero_iff.mpr (Or.inl two_pi_ne_zero), Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)]
  simp only [Complex.cpow_def_of_ne_zero two_pi_ne_zero, Complex.cpow_def_of_ne_zero two_ne_zero]
  simp only [← Complex.exp_add]
  congr 1
  ring

def reflectedSquareGammaContinuation (s : ℂ) : ℂ :=
  (2 : ℂ) ^ (2 * s - 1) * Complex.Gammaℂ (s / 2) *
    (Complex.Gammaℂ (1 - s / 2))⁻¹

private lemma gamma_half_differentiableAt (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s := by
  refine (Complex.differentiableAt_Gamma (s / 2) ?_).comp s
    (differentiableAt_id.div_const (2 : ℂ))
  intro m h
  have hpos : 0 < (s / 2).re := by
    rw [show (s / 2).re = s.re / 2 by simp [Complex.div_re]]
    linarith
  rw [h] at hpos
  simp at hpos
  exact absurd hpos (not_lt.mpr (Nat.cast_nonneg m))

theorem reflectedSquareGammaContinuation_differentiableOn :
    DifferentiableOn ℂ reflectedSquareGammaContinuation {s : ℂ | 0 < s.re} := by
  have h1 : DifferentiableOn ℂ (fun s : ℂ => (2 : ℂ) ^ (2 * s - 1)) {s : ℂ | 0 < s.re} :=
    DifferentiableOn.const_cpow (f := fun s : ℂ => 2 * s - 1)
      ((differentiable_id.const_mul 2).sub_const 1).differentiableOn (Or.inl two_ne_zero)
  have h2 : DifferentiableOn ℂ (fun s : ℂ => Complex.Gammaℂ (s / 2)) {s : ℂ | 0 < s.re} := by
    change DifferentiableOn ℂ
      (fun s : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-(s / 2)) * Complex.Gamma (s / 2))
      {s : ℂ | 0 < s.re}
    have hA2 : DifferentiableOn ℂ (fun s : ℂ => (2 * (Real.pi : ℂ)) ^ (-(s / 2)))
        {s : ℂ | 0 < s.re} :=
      DifferentiableOn.const_cpow (f := fun s : ℂ => -(s / 2))
        ((differentiable_id.div_const (2 : ℂ)).neg).differentiableOn (Or.inl two_pi_ne_zero)
    have hG : DifferentiableOn ℂ (fun s : ℂ => Complex.Gamma (s / 2)) {s : ℂ | 0 < s.re} :=
      fun s hs => (gamma_half_differentiableAt s hs).differentiableWithinAt
    exact ((differentiable_const (c := (2 : ℂ))).differentiableOn.mul hA2).mul hG
  have h3 : DifferentiableOn ℂ (fun s : ℂ => (Complex.Gammaℂ (1 - s / 2))⁻¹)
      {s : ℂ | 0 < s.re} :=
    (Complex.differentiable_Gammaℂ_inv.comp
      ((differentiable_const (1 : ℂ)).sub (differentiable_id.div_const (2 : ℂ)))).differentiableOn
  change DifferentiableOn ℂ (fun s : ℂ => (2 : ℂ) ^ (2 * s - 1) * Complex.Gammaℂ (s / 2) *
      (Complex.Gammaℂ (1 - s / 2))⁻¹) {s : ℂ | 0 < s.re}
  exact (h1.mul h2).mul h3

end DedekindZetaZeroFree.LargeSieve.Vendor

end
