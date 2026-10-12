module

public import DedekindZetaZeroFree.LFunctions.Dedekind.GammaFactors

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open Complex

theorem zetaGammaReciprocal_differentiable (K : Type) [Field K] [NumberField K] :
    Differentiable ℂ (zetaGammaReciprocal K) := by
  have hc : ((|NumberField.discr K| : ℤ) : ℂ) ≠ 0 := by
    simp [NumberField.discr_ne_zero K]
  unfold zetaGammaReciprocal
  refine Differentiable.mul (Differentiable.mul ?_ ?_) ?_
  · exact (differentiable_id.neg.div_const 2).const_cpow (Or.inl hc)
  · exact (Complex.differentiable_Gammaℝ_inv.pow _)
  · exact (Complex.differentiable_Gammaℂ_inv.pow _)

theorem zetaGammaReciprocal_zero (K : Type) [Field K] [NumberField K] :
    zetaGammaReciprocal K 0 = 0 := by
  have hsum := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  have hrank : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hGℝ : Complex.Gammaℝ 0 = 0 := by
    rw [Complex.Gammaℝ_eq_zero_iff]; exact ⟨0, by simp⟩
  have hGℂ : Complex.Gammaℂ 0 = 0 := by
    rw [Complex.Gammaℂ_def, (Complex.Gamma_eq_zero_iff 0).mpr ⟨0, by simp⟩, mul_zero]
  unfold zetaGammaReciprocal
  simp only [neg_zero, zero_div, cpow_zero, one_mul, hGℝ, hGℂ, inv_zero]
  rcases eq_or_ne (NumberField.InfinitePlace.nrRealPlaces K) 0 with h1 | h1
  · have h2 : NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 := by
      rw [h1] at hsum; omega
    rw [h1]
    simp only [pow_zero, one_mul]
    exact zero_pow h2
  · rw [zero_pow h1, zero_mul]

theorem zetaGammaReciprocal_mul_factor (K : Type) [Field K] [NumberField K]
    (s : ℂ) (hs : 1 < s.re) :
    zetaGammaReciprocal K s * zetaGammaFactor K s = 1 := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hc : ((|NumberField.discr K| : ℤ) : ℂ) ≠ 0 := by
    simp [NumberField.discr_ne_zero K]
  have hGℝ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs0
  have hGℂ : Complex.Gammaℂ s ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (cpow_ne_zero_iff.mpr (Or.inl (by norm_num))))
      (Complex.Gamma_ne_zero_of_re_pos hs0)
  have hc1 : ((|NumberField.discr K| : ℤ) : ℂ) ^ (-s / 2) *
      ((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2) = 1 := by
    rw [← cpow_add _ _ hc, show -s / 2 + s / 2 = 0 by ring, cpow_zero]
  have hℝ : (Complex.Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K *
      Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hGℝ, one_pow]
  have hℂ : (Complex.Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K *
      Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hGℂ, one_pow]
  unfold zetaGammaReciprocal zetaGammaFactor
  calc (((|NumberField.discr K| : ℤ) : ℂ) ^ (-s / 2) *
        (Complex.Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K *
        (Complex.Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K) *
      (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2) *
        Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K *
        Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K)
      = (((|NumberField.discr K| : ℤ) : ℂ) ^ (-s / 2) *
          ((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) *
        ((Complex.Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K *
          Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K) *
        ((Complex.Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K) := by ring
    _ = 1 := by rw [hc1, hℝ, hℂ]; ring

end DedekindZetaZeroFree.AbelianQuotient
