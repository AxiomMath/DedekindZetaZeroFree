module

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.ArchimedeanGaussianMellin

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

open MeasureTheory

private theorem square_cpow (a : ℝ) (ha : 0 < a) (z : ℂ) :
    ((a ^ 2 : ℝ) : ℂ) ^ z = (a : ℂ) ^ (2 * z) := by
  rw [pow_two, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le ha.le,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne')]
  congr 1
  ring

theorem integrableOn_gaussian_real_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    IntegrableOn (fun q : ℝ ↦
      (q : ℂ) ^ (s - 1) *
        Complex.exp (-((Real.pi * a ^ 2 : ℝ) : ℂ) * (q : ℂ) ^ 2))
      (Set.Ioi 0) := by
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, neg_mul] using
    AbelianQuotient.integrableOn_gaussian_real_place_mellin s (a ^ 2) hs
      (sq_pos_of_pos ha)

theorem gaussian_real_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    (∫ q : ℝ in Set.Ioi 0,
      (q : ℂ) ^ (s - 1) *
        Complex.exp (-((Real.pi * a ^ 2 : ℝ) : ℂ) * (q : ℂ) ^ 2)) =
      (1 / 2 : ℂ) * (a : ℂ) ^ (-s) * Complex.Gammaℝ s := by
  have h := AbelianQuotient.gaussian_real_place_mellin s (a ^ 2) hs
    (sq_pos_of_pos ha)
  rw [square_cpow a ha, show (2 : ℂ) * (-s / 2) = -s by ring] at h
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, neg_mul, one_div] using h

theorem integrableOn_gaussian_complex_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    IntegrableOn (fun q : ℝ ↦
      (q : ℂ) ^ (2 * s - 1) *
        Complex.exp (-((2 * Real.pi * a ^ 2 : ℝ) : ℂ) * (q : ℂ) ^ 2))
      (Set.Ioi 0) := by
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, neg_mul] using
    AbelianQuotient.integrableOn_gaussian_complex_place_mellin s (a ^ 2) hs
      (sq_pos_of_pos ha)

theorem gaussian_complex_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    (∫ q : ℝ in Set.Ioi 0,
      (q : ℂ) ^ (2 * s - 1) *
        Complex.exp (-((2 * Real.pi * a ^ 2 : ℝ) : ℂ) * (q : ℂ) ^ 2)) =
      (1 / 4 : ℂ) * (a : ℂ) ^ (-2 * s) * Complex.Gammaℂ s := by
  have h := AbelianQuotient.gaussian_complex_place_mellin s (a ^ 2) hs
    (sq_pos_of_pos ha)
  rw [square_cpow a ha, show (2 : ℂ) * (-s) = -2 * s by ring] at h
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, neg_mul, one_div] using h

end DedekindZetaZeroFree.AbelianQuotient.Theta
