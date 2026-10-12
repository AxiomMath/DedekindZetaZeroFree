module

public import DedekindZetaZeroFree.Analysis.ModifiedBesselKOneThird
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ComplexExceptionalFunctional

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxPlanarKernel

open MeasureTheory KPCplxCharacterHaar KPCplxBessel
open KPCplxJacquetFunctional KPCplxPrincipalSeriesCharts

noncomputable def planarSelfDualHaar (c : ℝ) : Measure ℂ :=
  ENNReal.ofReal (c / (2 * Real.pi)) • euclideanArea

noncomputable def besselCoefficient (c : ℝ) : ℝ :=
  (c / Real.Gamma (4 / 3 : ℝ)) * Real.rpow (c / 2) (1 / 3 : ℝ)

noncomputable def planarFourierKernel (c ρ : ℝ) (x : ℂ) : ℂ :=
  ((Real.rpow ρ (4 / 3 : ℝ) *
      Real.rpow (ρ ^ 2 + ‖x‖ ^ 2) (-(4 / 3 : ℝ)) : ℝ) : ℂ) *
    Complex.exp (-Complex.I * (c : ℂ) * (x.re : ℂ))

theorem characterHaar_eq_planarSelfDualHaar (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) :
    characterHaar β = planarSelfDualHaar c := by
  simp [characterHaar, characterScale, planarSelfDualHaar, hβ,
    Complex.norm_real, abs_of_pos hc]

theorem besselCoefficient_pos (c : ℝ) (hc : 0 < c) :
    0 < besselCoefficient c := by
  unfold besselCoefficient
  exact mul_pos (div_pos hc (Real.Gamma_pos_of_pos (by norm_num)))
    (Real.rpow_pos_of_pos (by linarith) _)

private theorem laplace_rpow (a : ℝ) (ha : 0 < a) :
    Real.rpow a (-(4 / 3 : ℝ)) =
      (Real.Gamma (4 / 3 : ℝ))⁻¹ *
        ∫ t in Set.Ioi (0 : ℝ), Real.rpow t (1 / 3 : ℝ) * Real.exp (-(a * t)) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (4 / 3 : ℝ)) (r := a) (by norm_num) ha
  have he : (4 / 3 : ℝ) - 1 = 1 / 3 := by norm_num
  rw [he] at h
  change (∫ t in Set.Ioi (0 : ℝ), Real.rpow t (1 / 3 : ℝ) * Real.exp (-(a * t))) =
    Real.rpow (1 / a) (4 / 3 : ℝ) * Real.Gamma (4 / 3 : ℝ) at h
  simp only [Real.rpow_eq_pow]
  simp only [Real.rpow_eq_pow] at h
  rw [h, one_div, Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
  have hg : Real.Gamma (4 / 3 : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 4 / 3)).ne'
  field_simp

private theorem oscillatory_gaussian (c t : ℝ) (ht : 0 < t) :
    (∫ x : ℂ, (Real.exp (-t * ‖x‖ ^ 2) : ℂ) *
      Complex.exp (-Complex.I * (c : ℂ) * (x.re : ℂ))) =
    (Real.pi / t : ℂ) * Complex.exp (-(c : ℂ) ^ 2 / (4 * (t : ℂ))) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (t : ℂ)) (by simpa using ht) (-Complex.I * (c : ℂ)) (1 : ℂ)
  simp only [Complex.finrank_real_complex, Nat.cast_ofNat, norm_one, one_pow,
    mul_one, show (2 : ℂ) / 2 = 1 by norm_num, Complex.cpow_one] at h
  calc
    _ = ∫ x : ℂ, Complex.exp (-(t : ℂ) * (‖x‖ : ℂ) ^ 2 +
        (-Complex.I * (c : ℂ)) * (inner ℝ (1 : ℂ) x : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
        Complex.ofReal_pow, Complex.exp_add]
      congr 2
      simp [Complex.inner]
    _ = _ := by
      rw [h]
      congr 2
      simp [mul_pow]

private theorem phase_norm (c : ℝ) (x : ℂ) :
    ‖Complex.exp (-Complex.I * (c : ℂ) * (x.re : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

private theorem gaussian_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : ℂ => Real.exp (-t * ‖x‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (t : ℂ)) (by simpa using ht) 0 (0 : ℂ)
  have h' := h.re
  convert h' using 1
  ext x
  simp [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
    ← Complex.ofReal_exp]

private theorem gaussian_integral (t : ℝ) (ht : 0 < t) :
    (∫ x : ℂ, Real.exp (-t * ‖x‖ ^ 2)) = Real.pi / t := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm
    (V := ℂ) (b := (t : ℂ)) (by simpa using ht)
  simp only [Complex.finrank_real_complex, Nat.cast_ofNat,
    show (2 : ℂ) / 2 = 1 by norm_num, Complex.cpow_one] at h
  have h' : (Complex.ofReal (∫ x : ℂ, Real.exp (-t * ‖x‖ ^ 2))) = (Real.pi / t : ℝ) := by
    rw [← integral_complex_ofReal]
    convert h using 1
    · congr 1; ext x
      rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]
    · simp
  exact Complex.ofReal_injective h'

noncomputable def laplaceGaussian (c ρ t : ℝ) (x : ℂ) : ℂ :=
  ((t ^ (1 / 3 : ℝ) * Real.exp (-(ρ ^ 2 * t)) : ℝ) : ℂ) *
    ((Real.exp (-t * ‖x‖ ^ 2) : ℂ) *
      Complex.exp (-Complex.I * (c : ℂ) * (x.re : ℂ)))

private theorem laplaceGaussian_integrable (c ρ : ℝ) (hρ : 0 < ρ) :
    Integrable (Function.uncurry (laplaceGaussian c ρ))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure ℂ)) := by
  have hm : AEStronglyMeasurable (Function.uncurry (laplaceGaussian c ρ))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure ℂ)) := by
    apply Continuous.aestronglyMeasurable
    unfold laplaceGaussian Function.uncurry
    fun_prop (disch := norm_num)
  apply (integrable_prod_iff hm).2
  constructor
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have h := (gaussian_integrable t ht).ofReal (𝕜 := ℂ)
    have hp := h.mul_bdd (c := 1)
      (by fun_prop : AEStronglyMeasurable
        (fun x : ℂ => Complex.exp (-Complex.I * (c : ℂ) * (x.re : ℂ))))
      (Filter.Eventually.of_forall fun x => le_of_eq (phase_norm c x))
    exact hp.const_mul ((t ^ (1 / 3 : ℝ) * Real.exp (-(ρ ^ 2 * t)) : ℝ) : ℂ)
  · have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (-(2 / 3 : ℝ))) (p := (1 : ℝ)) (b := ρ ^ 2)
      (by norm_num) (by norm_num) (sq_pos_of_pos hρ)
    have hi : IntegrableOn (fun t : ℝ => Real.pi *
        (t ^ (-(2 / 3 : ℝ)) * Real.exp (-(ρ ^ 2 * t)))) (Set.Ioi 0) := by
      change Integrable _ (volume.restrict (Set.Ioi 0))
      simpa only [Real.rpow_one, neg_mul] using h.const_mul Real.pi
    refine hi.congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    simp only [Function.uncurry, laplaceGaussian, norm_mul, phase_norm, mul_one,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)),
      abs_of_pos (Real.exp_pos _)]
    rw [abs_of_pos (Real.rpow_pos_of_pos ht (1 / 3 : ℝ))]
    rw [integral_const_mul, gaussian_integral t ht]
    have hpow : t ^ (1 / 3 : ℝ) / t = t ^ (-(2 / 3 : ℝ)) := by
      calc
        _ = t ^ (1 / 3 : ℝ) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_sub ht]; norm_num
    rw [← hpow]
    ring

private theorem laplaceGaussian_integral_t (c ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) :
    (∫ t in Set.Ioi (0 : ℝ), laplaceGaussian c ρ t x) =
      (Real.Gamma (4 / 3 : ℝ) : ℂ) *
        (Real.rpow (ρ ^ 2 + ‖x‖ ^ 2) (-(4 / 3 : ℝ)) : ℂ) *
          Complex.exp (-Complex.I * (c : ℂ) * (x.re : ℂ)) := by
  have ha : 0 < ρ ^ 2 + ‖x‖ ^ 2 := by positivity
  have hg : Real.Gamma (4 / 3 : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 4 / 3)).ne'
  have hl := laplace_rpow (ρ ^ 2 + ‖x‖ ^ 2) ha
  simp only [Real.rpow_eq_pow] at hl ⊢
  have he : (∫ t in Set.Ioi (0 : ℝ),
      t ^ (1 / 3 : ℝ) * Real.exp (-((ρ ^ 2 + ‖x‖ ^ 2) * t))) =
      Real.Gamma (4 / 3 : ℝ) * (ρ ^ 2 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ)) := by
    rw [hl]; field_simp
  calc
    _ = (∫ t in Set.Ioi (0 : ℝ),
        ((t ^ (1 / 3 : ℝ) * Real.exp (-((ρ ^ 2 + ‖x‖ ^ 2) * t)) : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * (c : ℂ) * (x.re : ℂ)) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with t
      unfold laplaceGaussian
      rw [← mul_assoc, ← Complex.ofReal_mul]
      congr 2
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring
    _ = _ := by rw [integral_complex_ofReal, he, Complex.ofReal_mul]

private theorem laplaceGaussian_integral_x (c ρ t : ℝ) (ht : 0 < t) :
    (∫ x : ℂ, laplaceGaussian c ρ t x) =
      ((Real.pi * (t ^ (-(2 / 3 : ℝ)) *
        Real.exp (-(ρ ^ 2 * t) - c ^ 2 / (4 * t))) : ℝ) : ℂ) := by
  unfold laplaceGaussian
  rw [integral_const_mul, oscillatory_gaussian c t ht]
  have he : -(c : ℂ) ^ 2 / (4 * (t : ℂ)) = ((-(c ^ 2 / (4 * t)) : ℝ) : ℂ) := by push_cast; ring
  rw [he, ← Complex.ofReal_exp, ← Complex.ofReal_div,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have hpow : t ^ (1 / 3 : ℝ) / t = t ^ (-(2 / 3 : ℝ)) := by
    calc
      _ = t ^ (1 / 3 : ℝ) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub ht]; norm_num
  apply congrArg Complex.ofReal
  rw [sub_eq_add_neg, Real.exp_add, ← hpow]
  ring

private theorem schlafli_scaled_integral (c ρ : ℝ) (hρ : 0 < ρ) :
    (∫ t in Set.Ioi (0 : ℝ),
      t ^ (-(2 / 3 : ℝ)) * Real.exp (-(ρ ^ 2 * t) - c ^ 2 / (4 * t))) =
      ρ ^ (-(2 / 3 : ℝ)) *
        ∫ u in Set.Ioi (0 : ℝ), schlafliKernel (-(2 / 3 : ℝ)) (c * ρ) u := by
  have hp : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have h := integral_comp_mul_left_Ioi
    (schlafliKernel (-(2 / 3 : ℝ)) (c * ρ)) 0 hp
  simp only [mul_zero, smul_eq_mul] at h
  have he : (∫ t in Set.Ioi (0 : ℝ),
      schlafliKernel (-(2 / 3 : ℝ)) (c * ρ) (ρ ^ 2 * t)) =
      (ρ ^ 2) ^ (-(2 / 3 : ℝ)) *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (-(2 / 3 : ℝ)) *
          Real.exp (-(ρ ^ 2 * t) - c ^ 2 / (4 * t)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp [schlafliKernel]
    rw [Real.mul_rpow hp.le (le_of_lt ht)]
    have he : (c * ρ) ^ 2 / (4 * (ρ ^ 2 * t)) = c ^ 2 / (4 * t) := by
      field_simp
    rw [he]
    ring
  rw [he] at h
  have hpw : (ρ ^ 2) ^ (-(2 / 3 : ℝ)) = ρ ^ (-(4 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  rw [hpw] at h
  have hpow : ρ ^ (-(4 / 3 : ℝ)) * ρ ^ (-(2 / 3 : ℝ)) = (ρ ^ 2)⁻¹ := by
    rw [← Real.rpow_add hρ]
    norm_num
  have hn : ρ ^ (-(4 / 3 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hρ _).ne'
  apply mul_left_cancel₀ hn
  rw [h, ← mul_assoc, hpow]

private theorem planar_laplace_transform (c ρ : ℝ) (hρ : 0 < ρ) :
    (∫ x : ℂ, planarFourierKernel c ρ x) =
      ((ρ ^ (4 / 3 : ℝ) * (Real.Gamma (4 / 3 : ℝ))⁻¹ * Real.pi *
        ρ ^ (-(2 / 3 : ℝ)) *
          ∫ u in Set.Ioi (0 : ℝ), schlafliKernel (-(2 / 3 : ℝ)) (c * ρ) u : ℝ) : ℂ) := by
  have hg : Real.Gamma (4 / 3 : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 4 / 3)).ne'
  have hswap := integral_integral_swap (laplaceGaussian_integrable c ρ hρ)
  calc
    _ = (ρ ^ (4 / 3 : ℝ) * (Real.Gamma (4 / 3 : ℝ))⁻¹ : ℝ) *
        ∫ x : ℂ, ∫ t in Set.Ioi (0 : ℝ), laplaceGaussian c ρ t x := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [laplaceGaussian_integral_t c ρ hρ x]
      simp only [planarFourierKernel, Real.rpow_eq_pow, Complex.ofReal_mul,
        Complex.ofReal_inv]
      have hg' : (Real.Gamma (4 / 3 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg
      field_simp
    _ = (ρ ^ (4 / 3 : ℝ) * (Real.Gamma (4 / 3 : ℝ))⁻¹ : ℝ) *
        ∫ t in Set.Ioi (0 : ℝ), ∫ x : ℂ, laplaceGaussian c ρ t x := by
      rw [hswap]
    _ = (ρ ^ (4 / 3 : ℝ) * (Real.Gamma (4 / 3 : ℝ))⁻¹ : ℝ) *
        ∫ t in Set.Ioi (0 : ℝ),
          ((Real.pi * (t ^ (-(2 / 3 : ℝ)) *
            Real.exp (-(ρ ^ 2 * t) - c ^ 2 / (4 * t))) : ℝ) : ℂ) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact laplaceGaussian_integral_x c ρ t ht
    _ = _ := by
      rw [integral_complex_ofReal, integral_const_mul, schlafli_scaled_integral c ρ hρ]
      push_cast
      ring

theorem planar_fourier_bessel (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    (∫ x : ℂ,
      ((Real.rpow ρ (4 / 3 : ℝ) *
        Real.rpow (ρ ^ 2 + ‖x‖ ^ 2) (-(4 / 3 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (-Complex.I * (c : ℂ) * (x.re : ℂ))
        ∂planarSelfDualHaar c) =
      ((besselCoefficient c * ρ * besselKThird (c * ρ) : ℝ) : ℂ) := by
  change (∫ x : ℂ, planarFourierKernel c ρ x ∂planarSelfDualHaar c) = _
  rw [planarSelfDualHaar, integral_smul_measure]
  change (ENNReal.ofReal (c / (2 * Real.pi))).toReal •
    (∫ x : ℂ, planarFourierKernel c ρ x) = _
  rw [ENNReal.toReal_ofReal (by positivity), planar_laplace_transform c ρ hρ]
  rw [besselCoefficient, besselKThird]
  simp only [Real.rpow_eq_pow]
  have hpow : ρ ^ (4 / 3 : ℝ) * ρ ^ (-(2 / 3 : ℝ)) = ρ ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add hρ]; norm_num
  have hcp : (c * ρ / 2) ^ (-(1 / 3 : ℝ)) =
      (c / 2) ^ (-(1 / 3 : ℝ)) * ρ ^ (-(1 / 3 : ℝ)) := by
    rw [show c * ρ / 2 = (c / 2) * ρ by ring]
    exact Real.mul_rpow (by positivity) hρ.le
  have hcancel : (c / 2) ^ (1 / 3 : ℝ) * (c / 2) ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add (by positivity)]; norm_num
  have hrho : ρ * ρ ^ (-(1 / 3 : ℝ)) = ρ ^ (2 / 3 : ℝ) := by
    calc
      _ = ρ ^ (1 : ℝ) * ρ ^ (-(1 / 3 : ℝ)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hρ]; norm_num
  have hreal : c / (2 * Real.pi) *
      (ρ ^ (4 / 3 : ℝ) * (Real.Gamma (4 / 3 : ℝ))⁻¹ * Real.pi *
        ρ ^ (-(2 / 3 : ℝ))) =
      c / Real.Gamma (4 / 3 : ℝ) * (c / 2) ^ (1 / 3 : ℝ) * ρ *
        (1 / 2 * (c * ρ / 2) ^ (-(1 / 3 : ℝ))) := by
    rw [hcp]
    calc
      _ = c / (2 * Real.Gamma (4 / 3 : ℝ)) * ρ ^ (2 / 3 : ℝ) := by
        rw [show ρ ^ (4 / 3 : ℝ) * (Real.Gamma (4 / 3 : ℝ))⁻¹ * Real.pi *
          ρ ^ (-(2 / 3 : ℝ)) =
          (ρ ^ (4 / 3 : ℝ) * ρ ^ (-(2 / 3 : ℝ))) *
            (Real.Gamma (4 / 3 : ℝ))⁻¹ * Real.pi by ring, hpow]
        field_simp
      _ = _ := by
        rw [show c / Real.Gamma (4 / 3 : ℝ) * (c / 2) ^ (1 / 3 : ℝ) * ρ *
            (1 / 2 * ((c / 2) ^ (-(1 / 3 : ℝ)) * ρ ^ (-(1 / 3 : ℝ)))) =
            c / (2 * Real.Gamma (4 / 3 : ℝ)) *
              ((c / 2) ^ (1 / 3 : ℝ) * (c / 2) ^ (-(1 / 3 : ℝ))) *
              (ρ * ρ ^ (-(1 / 3 : ℝ))) by ring, hcancel, hrho]
        ring
  rw [Complex.real_smul, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [← mul_assoc, hreal]
  ring

theorem jacquet_spherical_diagonal_eq_bessel (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (y : ℂˣ) :
    jacquetFunctional β
        (pi positiveParameter (Matrix.ProjGenLinGroup.mk (diagonal y))
          (sphericalSection positiveParameter)) =
      ((besselCoefficient c * ‖(y : ℂ)‖ * besselKThird (c * ‖(y : ℂ)‖) : ℝ) : ℂ) := by
  rw [jacquetFunctional_spherical_diagonal_positive c hc β hβ y,
    characterHaar_eq_planarSelfDualHaar c hc β hβ]
  exact planar_fourier_bessel c ‖(y : ℂ)‖ hc (norm_pos_iff.mpr y.ne_zero)

theorem jacquet_spherical_diagonal_positive (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (y : ℂˣ) :
    (jacquetFunctional β
      (pi positiveParameter (Matrix.ProjGenLinGroup.mk (diagonal y))
        (sphericalSection positiveParameter))).im = 0 ∧
      0 < (jacquetFunctional β
        (pi positiveParameter (Matrix.ProjGenLinGroup.mk (diagonal y))
          (sphericalSection positiveParameter))).re := by
  rw [jacquet_spherical_diagonal_eq_bessel c hc β hβ y]
  simp only [Complex.ofReal_im, Complex.ofReal_re]
  have hy : 0 < ‖(y : ℂ)‖ := norm_pos_iff.mpr y.ne_zero
  exact ⟨True.intro, mul_pos (mul_pos (besselCoefficient_pos c hc) hy)
    (besselKThird_pos (c * ‖(y : ℂ)‖) (mul_pos hc hy))⟩

end DedekindZetaZeroFree.KPCplxPlanarKernel
