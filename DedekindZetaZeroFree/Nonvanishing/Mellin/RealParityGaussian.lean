module

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.ArchimedeanGaussianMellin

@[expose] public section

noncomputable section

open MeasureTheory

namespace DedekindZetaZeroFree.AbelianQuotient

private theorem parity_square_cpow (a : ℝ) (s : ℂ) :
    ((a ^ 2 : ℝ) : ℂ) ^ (-s / 2) = ((|a| : ℝ) : ℂ) ^ (-s) := by
  rw [← sq_abs a, pow_two, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (abs_nonneg a) (abs_nonneg a),
    ← pow_two, ← Complex.cpow_mul_nat]
  congr 1
  ring

private theorem parity_odd_kernel (s : ℂ) (q a : ℝ) (hq : 0 < q) :
    ((q * a : ℝ) : ℂ) * (q : ℂ) ^ (s - 1) =
      (a : ℂ) * (q : ℂ) ^ ((s + 1) - 1) := by
  rw [show (s + 1) - 1 = 1 + (s - 1) by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hq.ne'),
    Complex.cpow_one, Complex.ofReal_mul]
  ring

private theorem parity_sign_abs (a : ℝ) (ha : a ≠ 0) :
    Real.sign a * |a| = a := by
  rcases ha.lt_or_gt with h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]
    ring
  · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]

private theorem parity_odd_cpow (a : ℝ) (ha : a ≠ 0) (s : ℂ) :
    (a : ℂ) * ((a ^ 2 : ℝ) : ℂ) ^ (-(s + 1) / 2) =
      (Real.sign a : ℂ) * ((|a| : ℝ) : ℂ) ^ (-s) := by
  have habs : ((|a| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr ha)
  have hsign : (a : ℂ) = (Real.sign a : ℂ) * ((|a| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, parity_sign_abs a ha]
  rw [parity_square_cpow, show -(s + 1) = -s - 1 by ring,
    Complex.cpow_sub _ _ habs, Complex.cpow_one, hsign]
  field_simp

theorem real_parityGaussian_integrableOn
    (s : ℂ) (hs : 0 < s.re) (a : ℝ) (ha : a ≠ 0) (e : Bool) :
    IntegrableOn (fun q : ℝ =>
      (if e then ((q * a : ℝ) : ℂ) else 1) * (q : ℂ) ^ (s - 1) *
        Complex.exp (-((Real.pi * a ^ 2 * q ^ 2 : ℝ) : ℂ)))
      (Set.Ioi 0) volume := by
  cases e with
  | false =>
    simpa using integrableOn_gaussian_real_place_mellin s (a ^ 2) hs (sq_pos_of_ne_zero ha)
  | true =>
    have hs' : 0 < (s + 1).re := by simpa using (by linarith : 0 < s.re + 1)
    have h := (integrableOn_gaussian_real_place_mellin (s + 1) (a ^ 2)
      hs' (sq_pos_of_ne_zero ha)).const_mul (a : ℂ)
    apply IntegrableOn.congr_fun h _ measurableSet_Ioi
    intro q hq
    dsimp only
    simp only [Bool.true_eq, ↓reduceIte]
    rw [parity_odd_kernel s q a hq]
    ring

theorem real_parityGaussian_mellin
    (s : ℂ) (hs : 0 < s.re) (a : ℝ) (ha : a ≠ 0) (e : Bool) :
    let η : ℂ := if e then 1 else 0
    let χ : ℂ := if e then (Real.sign a : ℂ) else 1
    (∫ q : ℝ in Set.Ioi 0,
      (if e then ((q * a : ℝ) : ℂ) else 1) * (q : ℂ) ^ (s - 1) *
        Complex.exp (-((Real.pi * a ^ 2 * q ^ 2 : ℝ) : ℂ))) =
      (2 : ℂ)⁻¹ * Complex.Gammaℝ (s + η) * χ * ((|a| : ℝ) : ℂ) ^ (-s) := by
  cases e with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, add_zero, mul_one]
    rw [gaussian_real_place_mellin s (a ^ 2) hs (sq_pos_of_ne_zero ha), parity_square_cpow]
    ring
  | true =>
    simp only [Bool.true_eq, ↓reduceIte]
    have hs' : 0 < (s + 1).re := by simpa using (by linarith : 0 < s.re + 1)
    have hk : (∫ q : ℝ in Set.Ioi 0,
        ((q * a : ℝ) : ℂ) * (q : ℂ) ^ (s - 1) *
          Complex.exp (-((Real.pi * a ^ 2 * q ^ 2 : ℝ) : ℂ))) =
        (a : ℂ) * (∫ q : ℝ in Set.Ioi 0,
          (q : ℂ) ^ ((s + 1) - 1) *
            Complex.exp (-((Real.pi * a ^ 2 * q ^ 2 : ℝ) : ℂ))) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro q hq
      dsimp only
      rw [parity_odd_kernel s q a hq]
      ring
    rw [hk, gaussian_real_place_mellin (s + 1) (a ^ 2) hs' (sq_pos_of_ne_zero ha)]
    calc
      _ = (2 : ℂ)⁻¹ * Complex.Gammaℝ (s + 1) *
          ((a : ℂ) * ((a ^ 2 : ℝ) : ℂ) ^ (-(s + 1) / 2)) := by ring
      _ = _ := by rw [parity_odd_cpow a ha s]; ring

end DedekindZetaZeroFree.AbelianQuotient

end
