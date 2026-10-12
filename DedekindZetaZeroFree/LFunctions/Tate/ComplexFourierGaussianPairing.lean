module

public import DedekindZetaZeroFree.LFunctions.Tate.ComplexTraceFourierMellinNormalization

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

private theorem gaussInt (t : ℝ) (ht : 0 < t) :
    Integrable (fun y : ℂ => (Real.exp (-2 * Real.pi * t * ‖y‖ ^ 2) : ℂ)) volume := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (2 * Real.pi * t : ℝ)) (by simp; positivity) 0 0
  simpa only [zero_mul, add_zero, Complex.ofReal_exp, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_pow, neg_mul] using h
private theorem kernelInt (f : ℂ → ℂ) (hf : IsComplexAnnular f) (t : ℝ) (ht : 0 < t) :
    Integrable (fun p : ℂ × ℂ => f p.1 *
      Complex.exp (((-4 * Real.pi * (p.1 * p.2).re : ℝ) : ℂ) * Complex.I) *
      (Real.exp (-2 * Real.pi * t * ‖p.2‖ ^ 2) : ℂ)) (volume.prod volume) := by
  have hfc : Continuous f := hf.1.continuous
  have hfi : Integrable f volume := hfc.integrable_of_hasCompactSupport hf.2.1
  apply (hfi.norm.mul_prod (gaussInt t ht).norm).mono
  · exact (by fun_prop : Continuous (fun p : ℂ × ℂ => f p.1 *
      Complex.exp (((-4 * Real.pi * (p.1 * p.2).re : ℝ) : ℂ) * Complex.I) *
      (Real.exp (-2 * Real.pi * t * ‖p.2‖ ^ 2) : ℂ))).aestronglyMeasurable
  · filter_upwards with p
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_norm]
    exact le_rfl
private theorem kernelEval (t : ℝ) (ht : 0 < t) (x : ℂ) :
    (∫ y : ℂ, Complex.exp (((-4 * Real.pi * (x * y).re : ℝ) : ℂ) * Complex.I) *
      (Real.exp (-2 * Real.pi * t * ‖y‖ ^ 2) : ℂ)) =
    (2 * (t : ℂ))⁻¹ * (Real.exp (-2 * Real.pi * ‖x‖ ^ 2 / t) : ℂ) := by
  have hinner (y : ℂ) : ⟪y, 2 * (starRingEnd ℂ) x⟫_ℝ = 2 * (x * y).re := by
    rw [Complex.inner]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    norm_num
    ring
  have hid : (fun y : ℂ => (Real.exp (-2 * Real.pi * t * ‖y‖ ^ 2) : ℂ)) =
    (fun y : ℂ => Complex.exp (-(2 * Real.pi * t : ℂ) * (‖y‖ : ℂ) ^ 2)) := by
    ext y
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hFour : (∫ y : ℂ, Complex.exp (((-4 * Real.pi * (x * y).re : ℝ) : ℂ) * Complex.I) *
      (Real.exp (-2 * Real.pi * t * ‖y‖ ^ 2) : ℂ)) =
    FourierTransform.fourier (fun y : ℂ => (Real.exp (-2 * Real.pi * t * ‖y‖ ^ 2) : ℂ))
      (2 * (starRingEnd ℂ) x) := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with y
    rw [hinner]
    simp only [smul_eq_mul]
    congr 2
    push_cast
    ring
  rw [hFour, hid, fourier_gaussian_innerProductSpace (by simp; positivity)]
  have hn : ‖(2 : ℂ) * (starRingEnd ℂ) x‖ = 2 * ‖x‖ := by
    simp [norm_mul, Complex.norm_conj]
  rw [hn]
  simp only [Complex.finrank_real_complex]
  norm_num
  congr 1
  · have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    field_simp
  · congr 1
    push_cast
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    field_simp

theorem complexTraceFourier_gaussian_pairing (f : ℂ → ℂ) (hf : IsComplexAnnular f)
    (t : ℝ) (ht : 0 < t) :
    (∫ y : ℂ, complexTraceFourier f y *
      (Real.exp (-2 * Real.pi * t * ‖y‖ ^ 2) : ℂ) ∂(volume : Measure ℂ)) =
    (t : ℂ)⁻¹ * (∫ x : ℂ, f x *
      (Real.exp (-2 * Real.pi * ‖x‖ ^ 2 / t) : ℂ) ∂(volume : Measure ℂ)) := by
  calc
    _ = 2 * ∫ y : ℂ, ∫ x : ℂ, f x *
        Complex.exp (((-4 * Real.pi * (x * y).re : ℝ) : ℂ) * Complex.I) *
        (Real.exp (-2 * Real.pi * t * ‖y‖ ^ 2) : ℂ) := by
      simp only [integral_mul_const, complexTraceFourier]
      simp only [mul_assoc, integral_const_mul]
    _ = 2 * ∫ x : ℂ, ∫ y : ℂ, f x *
        Complex.exp (((-4 * Real.pi * (x * y).re : ℝ) : ℂ) * Complex.I) *
        (Real.exp (-2 * Real.pi * t * ‖y‖ ^ 2) : ℂ) := by
      rw [← integral_integral_swap (kernelInt f hf t ht)]
    _ = 2 * ∫ x : ℂ, f x * ((2 * (t : ℂ))⁻¹ *
        (Real.exp (-2 * Real.pi * ‖x‖ ^ 2 / t) : ℂ)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      rw [show (∫ y : ℂ, f x *
        Complex.exp (((-4 * Real.pi * (x * y).re : ℝ) : ℂ) * Complex.I) *
        (Real.exp (-2 * Real.pi * t * ‖y‖ ^ 2) : ℂ)) =
        f x * ∫ y : ℂ,
        Complex.exp (((-4 * Real.pi * (x * y).re : ℝ) : ℂ) * Complex.I) *
        (Real.exp (-2 * Real.pi * t * ‖y‖ ^ 2) : ℂ) by
          simp only [mul_assoc, integral_const_mul]]
      rw [kernelEval t ht x]
    _ = _ := by
      rw [show (fun x : ℂ => f x * ((2 * (t : ℂ))⁻¹ *
        (Real.exp (-2 * Real.pi * ‖x‖ ^ 2 / t) : ℂ))) =
        (fun x : ℂ => (2 * (t : ℂ))⁻¹ * (f x *
        (Real.exp (-2 * Real.pi * ‖x‖ ^ 2 / t) : ℂ))) by ext x; ring]
      rw [integral_const_mul, ← mul_assoc]
      congr 1
      simp only [mul_inv_rev]
      ring

end
end DedekindZetaZeroFree
