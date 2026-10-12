module

public import DedekindZetaZeroFree.Analysis.Gamma.ReciprocalRecurrenceAndRisingProducts
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.DerivativeIntegrationByParts

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.Vendor

def originMellinChart (h : ℝ → ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  ((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) *
    mellin (iteratedDeriv n h) (s + (n : ℂ)) *
    (Complex.Gammaℂ (s + (n : ℂ)))⁻¹

theorem originMellinChart_differentiableAt (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (n : ℕ) (s : ℂ)
    (hs : -(n : ℝ) < s.re) :
    DifferentiableAt ℂ (originMellinChart h n) s := by
  have ht : 0 < (s + (n : ℂ)).re := by
    rw [show (s + (n : ℂ)).re = s.re + (n : ℝ) by simp [Complex.add_re]]
    linarith
  have hm : DifferentiableAt ℂ
      (fun z : ℂ => mellin (iteratedDeriv n h) (z + (n : ℂ))) s :=
    (differentiableAt_comp_add_const (f := mellin (iteratedDeriv n h))
      (a := s) (b := (n : ℂ))).2
      (differentiableAt_mellin_iteratedDeriv_of_pos hh hc n ht)
  have hg : DifferentiableAt ℂ
      (fun z : ℂ => (Complex.Gammaℂ (z + (n : ℂ)))⁻¹) s :=
    (differentiableAt_comp_add_const (f := fun w : ℂ => (Complex.Gammaℂ w)⁻¹)
      (a := s) (b := (n : ℂ))).2
      (Complex.differentiable_Gammaℂ_inv.differentiableAt)
  have hmain : DifferentiableAt ℂ
      (fun z : ℂ => ((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) *
        mellin (iteratedDeriv n h) (z + (n : ℂ)) *
        (Complex.Gammaℂ (z + (n : ℂ)))⁻¹) s :=
    ((differentiableAt_const ((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n)).mul hm).mul hg
  rw [show originMellinChart h n = (fun z : ℂ =>
      ((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) *
        mellin (iteratedDeriv n h) (z + (n : ℂ)) *
        (Complex.Gammaℂ (z + (n : ℂ)))⁻¹) from rfl]
  exact hmain

theorem originMellinChart_succ (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (n : ℕ) (s : ℂ)
    (hs : -(n : ℝ) < s.re) :
    originMellinChart h (n + 1) s = originMellinChart h n s := by
  have ht : 0 < (s + (n : ℂ)).re := by
    rw [show (s + (n : ℂ)).re = s.re + (n : ℝ) by simp [Complex.add_re]]
    linarith
  have hg : ContDiff ℝ ∞ (iteratedDeriv n h) := contDiff_iteratedDeriv h hh n
  have hgc : HasCompactSupport (iteratedDeriv n h) := hasCompactSupport_iteratedDeriv h hc n
  have hcast : s + ((n + 1 : ℕ) : ℂ) = (s + (n : ℂ)) + 1 := by push_cast; ring
  have hA : originMellinChart h (n + 1) s =
      ((-1 : ℂ) ^ (n + 1) / (2 * (Real.pi : ℂ)) ^ (n + 1)) *
        (-(s + (n : ℂ)) * mellin (iteratedDeriv n h) (s + (n : ℂ))) *
        (Complex.Gammaℂ ((s + (n : ℂ)) + 1))⁻¹ := by
    simp only [originMellinChart, hcast, iteratedDeriv_succ]
    rw [mellin_deriv_eq_neg_mul (iteratedDeriv n h) hg hgc (s + (n : ℂ)) ht]
  have hCn : ((-1 : ℂ) ^ (n + 1) / (2 * (Real.pi : ℂ)) ^ (n + 1)) * (-(s + (n : ℂ)))
      = ((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) *
          ((s + (n : ℂ)) / (2 * (Real.pi : ℂ))) := by
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero two_ne_zero this
    rw [pow_succ, pow_succ]
    field_simp
  rw [hA, show originMellinChart h n s =
      ((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) *
        mellin (iteratedDeriv n h) (s + (n : ℂ)) *
        (Complex.Gammaℂ (s + (n : ℂ)))⁻¹ from rfl,
    inverse_Gammaℂ_recurrence (s + (n : ℂ))]
  exact calc
    ((-1 : ℂ) ^ (n + 1) / (2 * (Real.pi : ℂ)) ^ (n + 1)) *
        (-(s + (n : ℂ)) * mellin (iteratedDeriv n h) (s + (n : ℂ))) *
        (Complex.Gammaℂ ((s + (n : ℂ)) + 1))⁻¹
      = (((-1 : ℂ) ^ (n + 1) / (2 * (Real.pi : ℂ)) ^ (n + 1)) * (-(s + (n : ℂ)))) *
          (mellin (iteratedDeriv n h) (s + (n : ℂ)) *
            (Complex.Gammaℂ ((s + (n : ℂ)) + 1))⁻¹) := by ring
    _ = (((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) *
            ((s + (n : ℂ)) / (2 * (Real.pi : ℂ)))) *
          (mellin (iteratedDeriv n h) (s + (n : ℂ)) *
            (Complex.Gammaℂ ((s + (n : ℂ)) + 1))⁻¹) := by rw [hCn]
    _ = ((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) *
          mellin (iteratedDeriv n h) (s + (n : ℂ)) *
          (((s + (n : ℂ)) / (2 * (Real.pi : ℂ))) *
            (Complex.Gammaℂ ((s + (n : ℂ)) + 1))⁻¹) := by ring

end DedekindZetaZeroFree.LargeSieve.Vendor

end
