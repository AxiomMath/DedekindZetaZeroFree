module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

noncomputable section

open MeasureTheory

namespace DedekindZetaZeroFree.AbelianQuotient

def E (x : ℝ) : ℂ :=
  Complex.exp (-((Real.pi * x ^ 2 : ℝ) : ℂ))

def O (x : ℝ) : ℂ := (x : ℂ) * E x

theorem real_evenGaussian_integrable :
    Integrable (fun x : ℝ => Complex.exp (-((Real.pi * x ^ 2 : ℝ) : ℂ))) volume := by
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, neg_mul] using
    (integrable_cexp_neg_mul_sq (b := (Real.pi : ℂ))
      (by simpa using Real.pi_pos))

theorem real_oddGaussian_integrable :
    Integrable (fun x : ℝ =>
      (x : ℂ) * Complex.exp (-((Real.pi * x ^ 2 : ℝ) : ℂ))) volume := by
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, neg_mul] using
    (integrable_mul_cexp_neg_mul_sq (b := (Real.pi : ℂ))
      (by simpa using Real.pi_pos))

theorem real_evenGaussian_fourier :
    FourierTransform.fourier
      (fun x : ℝ => Complex.exp (-((Real.pi * x ^ 2 : ℝ) : ℂ))) =
      (fun ξ : ℝ => Complex.exp (-((Real.pi * ξ ^ 2 : ℝ) : ℂ))) := by
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, neg_mul, mul_one,
    div_one, Complex.one_cpow, one_mul] using
    (fourier_gaussian_pi (b := (1 : ℂ)) (by simp))

private theorem deriv_E (x : ℝ) : deriv E x = (-2 * (Real.pi : ℂ)) * O x := by
  have h : HasDerivAt (fun y : ℝ => -(Real.pi * y ^ 2))
      (-(Real.pi * (2 * x))) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul Real.pi).neg using 1
    · rfl
    · simp
  have hc := h.ofReal_comp.cexp
  have he : E = (fun y : ℝ => Complex.exp ↑(-(Real.pi * y ^ 2))) := by
    ext y
    simp [E]
  rw [he, hc.deriv]
  simp only [E, O, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

theorem real_oddGaussian_fourier :
    FourierTransform.fourier
      (fun x : ℝ => (x : ℂ) * Complex.exp (-((Real.pi * x ^ 2 : ℝ) : ℂ))) =
      (fun ξ : ℝ =>
        -Complex.I * ((ξ : ℂ) * Complex.exp (-((Real.pi * ξ ^ 2 : ℝ) : ℂ)))) := by
  change FourierTransform.fourier O = fun ξ => -Complex.I * O ξ
  have hE : FourierTransform.fourier E = E := real_evenGaussian_fourier
  have hO : Integrable (fun x : ℝ => x • E x) := by
    simpa only [Complex.real_smul, E] using real_oddGaussian_integrable
  have h := Real.deriv_fourier (f := E) real_evenGaussian_integrable hO
  rw [hE] at h
  have hf : (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * x) • E x) =
      (-2 * (Real.pi : ℂ) * Complex.I) • O := by
    ext x
    simp [O, smul_eq_mul, mul_assoc]
  have hs : FourierTransform.fourier ((-2 * (Real.pi : ℂ) * Complex.I) • O) =
      (-2 * (Real.pi : ℂ) * Complex.I) • FourierTransform.fourier O :=
    VectorFourier.fourierIntegral_const_smul _ _ _ _ _
  rw [hf, hs] at h
  ext x
  have hx := congrFun h x
  rw [deriv_E] at hx
  change (-2 * (Real.pi : ℂ)) * O x =
    (-2 * (Real.pi : ℂ) * Complex.I) * FourierTransform.fourier O x at hx
  have hc : (-2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  apply mul_left_cancel₀ hc
  rw [← hx]
  ring_nf
  simp [Complex.I_sq]

end DedekindZetaZeroFree.AbelianQuotient

end
