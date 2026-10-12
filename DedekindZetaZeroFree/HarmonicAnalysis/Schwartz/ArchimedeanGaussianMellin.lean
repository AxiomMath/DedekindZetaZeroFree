module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

/-
The two generic square-Gaussian computations below are adapted from LeanPool's
`Odlyzko/CompletedZeta/UnitAveragedGaussian.lean`, commit
`68aa6ee63d20ad76bcc15f595adfc72949991f06`, copyright (c) 2026 The FLT Project,
released under the Apache 2.0 license. See the project's vendored license.
-/

namespace DedekindZetaZeroFree.AbelianQuotient

open MeasureTheory

private theorem integrable_square_gaussian {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (2 * s - 1) * Complex.exp (-((r * x ^ 2 : ℝ) : ℂ)))
      (Set.Ioi 0) := by
  have hbase : MellinConvergent (fun t : ℝ => Complex.exp (-(t : ℂ))) s := by
    rw [MellinConvergent]
    convert Complex.GammaIntegral_convergent hs using 1
    ext t
    simp [mul_comm]
  have hscaled : MellinConvergent
      (fun t : ℝ => Complex.exp (-((r * t : ℝ) : ℂ))) s := by
    simpa only [Complex.ofReal_mul] using
      (MellinConvergent.comp_mul_left (f :=
        fun t : ℝ => Complex.exp (-(t : ℂ))) (s := s) hr).2 hbase
  have hsquare : MellinConvergent
      (fun t : ℝ => Complex.exp (-((r * t ^ 2 : ℝ) : ℂ))) (2 * s) := by
    have h := (MellinConvergent.comp_rpow
      (f := fun t : ℝ => Complex.exp (-((r * t : ℝ) : ℂ)))
      (s := 2 * s) (a := 2) (by norm_num)).2
    simp_all
  simpa only [MellinConvergent, smul_eq_mul] using hsquare

private theorem integral_square_gaussian {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Set.Ioi 0,
      (x : ℂ) ^ (2 * s - 1) * Complex.exp (-((r * x ^ 2 : ℝ) : ℂ))) =
      (2 : ℂ)⁻¹ * (1 / r : ℂ) ^ s * Complex.Gamma s := by
  have hsq := mellin_comp_rpow
    (f := fun t : ℝ => Complex.exp (-(r * t))) (2 * s) 2
  rw [show (2 * s) / (2 : ℝ) = s by norm_num] at hsq
  have hgamma := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
  rw [mellin] at hsq
  rw [mellin] at hsq
  simp only [smul_eq_mul, Complex.real_smul] at hsq
  rw [hgamma] at hsq
  have htwo : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  simpa only [htwo, Complex.ofReal_inv, Complex.ofReal_ofNat,
    Complex.ofReal_pow, Complex.ofReal_mul, one_div, Real.rpow_two, mul_assoc] using hsq

private theorem inverse_cpow {r : ℝ} (hr : 0 < r) (s : ℂ) :
    (1 / r : ℂ) ^ s = (r : ℂ) ^ (-s) := by
  rw [one_div, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact Real.pi_ne_zero.symm), Complex.cpow_neg]

theorem integrableOn_gaussian_real_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    IntegrableOn (fun q : ℝ =>
      (q : ℂ) ^ (s - 1) * Complex.exp (-((Real.pi * a * q ^ 2 : ℝ) : ℂ)))
      (Set.Ioi 0) := by
  have hs' : 0 < (s / 2).re := by simpa using half_pos hs
  have htwo : (2 : ℂ) * (s / 2) = s := by ring
  simpa only [htwo] using integrable_square_gaussian hs' (mul_pos Real.pi_pos ha)

theorem gaussian_real_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    (∫ q : ℝ in Set.Ioi 0,
      (q : ℂ) ^ (s - 1) * Complex.exp (-((Real.pi * a * q ^ 2 : ℝ) : ℂ))) =
      (2 : ℂ)⁻¹ * (a : ℂ) ^ (-s / 2) * Complex.Gammaℝ s := by
  have hs' : 0 < (s / 2).re := by simpa using half_pos hs
  have h := integral_square_gaussian hs' (mul_pos Real.pi_pos ha)
  simp only [mul_div_cancel₀ _ (by norm_num : (2 : ℂ) ≠ 0)] at h
  rw [h, inverse_cpow (mul_pos Real.pi_pos ha), Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le ha.le, Complex.Gammaℝ]
  rw [neg_div]
  ring

theorem integrableOn_gaussian_complex_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    IntegrableOn (fun q : ℝ =>
      (q : ℂ) ^ (2 * s - 1) * Complex.exp (-((2 * Real.pi * a * q ^ 2 : ℝ) : ℂ)))
      (Set.Ioi 0) := by
  exact integrable_square_gaussian hs (mul_pos (mul_pos (by norm_num) Real.pi_pos) ha)

theorem gaussian_complex_place_mellin (s : ℂ) (a : ℝ)
    (hs : 0 < s.re) (ha : 0 < a) :
    (∫ q : ℝ in Set.Ioi 0,
      (q : ℂ) ^ (2 * s - 1) * Complex.exp (-((2 * Real.pi * a * q ^ 2 : ℝ) : ℂ))) =
      (4 : ℂ)⁻¹ * (a : ℂ) ^ (-s) * Complex.Gammaℂ s := by
  rw [integral_square_gaussian hs (mul_pos (mul_pos (by norm_num) Real.pi_pos) ha),
    inverse_cpow (mul_pos (mul_pos (by norm_num) Real.pi_pos) ha),
    Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) ha.le,
    Complex.Gammaℂ, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

end DedekindZetaZeroFree.AbelianQuotient
