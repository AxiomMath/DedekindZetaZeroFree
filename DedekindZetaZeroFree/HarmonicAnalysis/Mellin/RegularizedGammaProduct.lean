module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.EntireRegularizedQuotient

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.Vendor

private lemma Gammaℂ_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    Complex.Gammaℂ s ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_
  · exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  · intro h0
    rw [Complex.Gamma_eq_zero_iff] at h0
    obtain ⟨m, hm⟩ := h0
    exact hs (by rw [hm]; simp)

private lemma Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    Complex.Gammaℂ s ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))))
    (Complex.Gamma_ne_zero_of_re_pos hs)

theorem originMellinQ_zero (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    originMellinQ h 0 = h 0 / (2 : ℂ) := by
  rw [originMellinQ_eq_chart h hh hc 1 0 (by norm_num)]
  rw [originMellinChart]
  have hm : mellin (deriv h) (1 : ℂ) = -h 0 := by
    rw [mellin]
    simp only [sub_self, Complex.cpow_zero, one_smul]
    exact integral_Ioi_deriv_eq_neg_at_zero h hh hc
  simp only [iteratedDeriv_one, pow_one, zero_add, Nat.cast_one]
  rw [hm, Complex.Gammaℂ_one]
  field_simp

theorem Gammaℂ_mul_originMellinQ_eq_mellin (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (s : ℂ) (hs : 0 < s.re) :
    Complex.Gammaℂ s * originMellinQ h s = mellin h s := by
  rw [originMellinQ_eq_mellin_div_Gammaℂ h hh hc s hs]
  field_simp [Gammaℂ_ne_zero_of_re_pos hs]

theorem Gammaℂ_mul_originMellinQ_eq_shift (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (n : ℕ) (s : ℂ) (hs : -(n : ℝ) < s.re) (hsi : s.im ≠ 0) :
    Complex.Gammaℂ s * originMellinQ h s =
      ((-1 : ℂ) ^ n * mellin (iteratedDeriv n h) (s + (n : ℂ))) /
        (∏ j ∈ Finset.range n, (s + (j : ℂ))) := by
  rw [originMellinQ_eq_chart h hh hc n s hs, originMellinChart]
  have hGamS : Complex.Gammaℂ s ≠ 0 := Gammaℂ_ne_zero_of_im_ne_zero hsi
  have hkey : Complex.Gammaℂ s * (Complex.Gammaℂ (s + (n : ℂ)))⁻¹ =
      (2 * (Real.pi : ℂ)) ^ n / (∏ j ∈ Finset.range n, (s + (j : ℂ))) := by
    rw [Gammaℂ_add_nat_rising_product s n hsi]
    field_simp
  calc Complex.Gammaℂ s *
        (((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) * mellin (iteratedDeriv n h) (s + (n : ℂ)) *
          (Complex.Gammaℂ (s + (n : ℂ)))⁻¹)
      = ((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) * mellin (iteratedDeriv n h) (s + (n : ℂ)) *
          (Complex.Gammaℂ s * (Complex.Gammaℂ (s + (n : ℂ)))⁻¹) := by ring
    _ = ((-1 : ℂ) ^ n / (2 * (Real.pi : ℂ)) ^ n) * mellin (iteratedDeriv n h) (s + (n : ℂ)) *
          ((2 * (Real.pi : ℂ)) ^ n / (∏ j ∈ Finset.range n, (s + (j : ℂ)))) := by rw [hkey]
    _ = ((-1 : ℂ) ^ n * mellin (iteratedDeriv n h) (s + (n : ℂ))) /
          (∏ j ∈ Finset.range n, (s + (j : ℂ))) := by
        field_simp

end DedekindZetaZeroFree.LargeSieve.Vendor

end
