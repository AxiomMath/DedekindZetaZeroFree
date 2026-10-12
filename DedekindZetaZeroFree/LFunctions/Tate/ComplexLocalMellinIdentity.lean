module

public import DedekindZetaZeroFree.LFunctions.Tate.ComplexFourierGaussianPairing

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open MeasureTheory

theorem complexAnnular_normMellin_integrable (f : ℂ → ℂ) (hf : IsComplexAnnular f)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    Integrable (complexNormMellinIntegrand f (1 - s)) (volume : Measure ℂ) := by
  obtain ⟨hcont, hcomp, a, b, ha, hab, hsupp⟩ := hf

  let w : ℂ → ℝ := fun x => (max (‖x‖ ^ 2) (a ^ 2)) ^ ((1 - s) - 1)
  have hw : Continuous w := by
    apply Continuous.rpow_const ((continuous_norm.pow 2).max continuous_const)
    intro x
    left
    exact ne_of_gt (lt_of_lt_of_le (sq_pos_of_pos ha) (le_max_right _ _))
  have hi : Integrable (fun x => f x * (w x : ℂ)) (volume : Measure ℂ) :=
    (hcont.continuous.mul (Complex.continuous_ofReal.comp hw)).integrable_of_hasCompactSupport
      (hcomp.mul_right)
  apply hi.congr
  filter_upwards with x
  by_cases hx : f x = 0
  · simp [complexNormMellinIntegrand, hx]
  · have hxs : x ∈ tsupport f := subset_tsupport f hx
    have hax : a ≤ ‖x‖ := (hsupp hxs).1
    have hx0 : x ≠ 0 := by
      intro hx0
      simpa [hx0] using ha.trans_le hax
    simp only [complexNormMellinIntegrand, if_neg hx0, w]
    rw [max_eq_left (sq_le_sq₀ ha.le (norm_nonneg x) |>.2 hax)]

private theorem schwartz_normMellin_integrable (g : SchwartzMap ℂ ℂ)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    Integrable (complexNormMellinIntegrand g s) (volume : Measure ℂ) := by
  have hmeas : AEStronglyMeasurable (complexNormMellinIntegrand g s)
      (volume : Measure ℂ) := by
    apply Measurable.aestronglyMeasurable
    exact Measurable.ite (measurableSet_singleton 0) measurable_const
      (g.continuous.measurable.mul (Complex.measurable_ofReal.comp
        ((measurable_norm.pow_const 2).pow_const _)))
  have hnorm (x : ℂ) (hx : x ≠ 0) :
      ‖complexNormMellinIntegrand g s x‖ = ‖g x‖ * ‖x‖ ^ (2 * (s - 1)) := by
    simp only [complexNormMellinIntegrand, if_neg hx, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (sq_nonneg _) _)]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (norm_nonneg x)]
    norm_num

  have hnear : IntegrableOn (complexNormMellinIntegrand g s)
      (Metric.ball 0 1) (volume : Measure ℂ) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp)
      (C := SchwartzMap.seminorm ℂ 0 0 g) (α := 2 * (1 - s))
      (by simp; linarith) _ hmeas
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x = 0
    · simp only [hx, complexNormMellinIntegrand, ↓reduceIte, norm_zero]
      exact mul_nonneg (apply_nonneg _ _) (Real.rpow_nonneg (by norm_num) _)
    · rw [hnorm x hx]
      have he : -(2 * (1 - s)) = 2 * (s - 1) := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (g.norm_le_seminorm ℂ x)
        (Real.rpow_nonneg (norm_nonneg x) _)

  have hfar : IntegrableOn (complexNormMellinIntegrand g s)
      (Metric.ball 0 1)ᶜ (volume : Measure ℂ) := by
    apply (g.integrable (μ := (volume : Measure ℂ))).norm.restrict.mono' hmeas.restrict
    filter_upwards [self_mem_ae_restrict (measurableSet_ball.compl)] with x hx
    have hnx : 1 ≤ ‖x‖ := by simpa using hx
    have hx0 : x ≠ 0 := by intro h; norm_num [h] at hnx
    rw [hnorm x hx0]
    have hpow : ‖x‖ ^ (2 * (s - 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hnx (by linarith)
    simpa using mul_le_mul_of_nonneg_left hpow (norm_nonneg (g x))
  have hu := hnear.union hfar
  simpa using hu

theorem complexTraceFourier_normMellin_integrable (f : ℂ → ℂ)
    (hf : IsComplexAnnular f) (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    Integrable (complexNormMellinIntegrand (complexTraceFourier f) s)
      (volume : Measure ℂ) := by
  let fS : SchwartzMap ℂ ℂ := hf.2.1.toSchwartzMap hf.1
  let L : ℂ ≃L[ℝ] ℂ := (Units.mk0 (2 : ℝ) (by norm_num)) • Complex.conjCLE
  let g : SchwartzMap ℂ ℂ := (2 : ℂ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L (FourierTransform.fourier fS))
  have hg : (g : ℂ → ℂ) = complexTraceFourier f := by
    funext x
    simp only [g, SchwartzMap.smul_apply,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      smul_eq_mul, SchwartzMap.fourier_coe, complexTraceFourier_eq_fourier]
    congr 2
  rw [← hg]
  exact schwartz_normMellin_integrable g s hs hs1

namespace ComplexTateLaplace
open Set
lemma laplace_integrable (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < a - 1)
      (by norm_num : 0 < (1 : ℝ)) hr)

lemma laplace_weight (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, t ^ (a - 1) * Real.exp (-(r * t))) =
      r ^ (-a) * Real.Gamma a := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr]
  simp [one_div, Real.inv_rpow hr.le, Real.rpow_neg hr.le]

lemma mellin_weight (a : ℝ) (x : ℂ) (hx : x ≠ 0) :
    (2 * Real.pi * ‖x‖ ^ 2) ^ (-a) =
      (2 * Real.pi) ^ (-a) * (‖x‖ ^ 2) ^ ((1 - a) - 1) := by
  rw [Real.mul_rpow (by positivity) (by positivity)]
  congr 2
  ring

lemma laplace_norm (g : ℂ → ℂ) (a : ℝ) (ha : 0 < a) (x : ℂ) (hx : x ≠ 0) :
    (∫ t : ℝ in Ioi 0,
      ‖g x * ((t ^ (a - 1) * Real.exp (-(2 * Real.pi * ‖x‖ ^ 2 * t)) : ℝ) : ℂ)‖) =
      ((2 * Real.pi) ^ (-a) * Real.Gamma a) *
        ‖complexNormMellinIntegrand g (1 - a) x‖ := by
  have hp : 0 < 2 * Real.pi * ‖x‖ ^ 2 := by positivity
  have he (t : ℝ) (ht : t ∈ Ioi 0) :
      ‖g x * ((t ^ (a - 1) * Real.exp (-(2 * Real.pi * ‖x‖ ^ 2 * t)) : ℝ) : ℂ)‖ =
        ‖g x‖ * (t ^ (a - 1) * Real.exp (-(2 * Real.pi * ‖x‖ ^ 2 * t))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  rw [setIntegral_congr_fun measurableSet_Ioi he]
  rw [integral_const_mul, laplace_weight a _ ha hp, mellin_weight a x hx]
  simp only [complexNormMellinIntegrand, if_neg hx, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (sq_nonneg _) _)]
  ring

lemma laplace_prod_integrable (g : ℂ → ℂ) (hg : AEStronglyMeasurable g volume)
    (a : ℝ) (ha : 0 < a)
    (hi : Integrable (complexNormMellinIntegrand g (1 - a)) volume) :
    Integrable (fun p : ℂ × ℝ =>
      g p.1 * ((p.2 ^ (a - 1) * Real.exp (-(2 * Real.pi * ‖p.1‖ ^ 2 * p.2)) : ℝ) : ℂ))
        (volume.prod (volume.restrict (Ioi 0))) := by
  apply (integrable_prod_iff ?_).mpr
  · refine ⟨?_, ?_⟩
    · filter_upwards [(volume : Measure ℂ).ae_ne (0 : ℂ)] with x hx
      exact ((laplace_integrable a (2 * Real.pi * ‖x‖ ^ 2) ha (by positivity)).ofReal).const_mul (g x)
    · apply (hi.norm.const_mul ((2 * Real.pi) ^ (-a) * Real.Gamma a)).congr
      filter_upwards [(volume : Measure ℂ).ae_ne (0 : ℂ)] with x hx
      exact (laplace_norm g a ha x hx).symm
  · exact (hg.comp_fst).mul
      ((Complex.measurable_ofReal.comp
        ((measurable_snd.pow_const _).mul
          (Real.measurable_exp.comp (by fun_prop)))).aestronglyMeasurable)

lemma laplace_mellin (g : ℂ → ℂ) (hg : AEStronglyMeasurable g volume)
    (a : ℝ) (ha : 0 < a)
    (hi : Integrable (complexNormMellinIntegrand g (1 - a)) volume) :
    (∫ t : ℝ in Ioi 0, ((t ^ (a - 1) : ℝ) : ℂ) *
      (∫ x : ℂ, g x * (Real.exp (-(2 * Real.pi * ‖x‖ ^ 2 * t)) : ℂ))) =
      (((2 * Real.pi) ^ (-a) * Real.Gamma a : ℝ) : ℂ) *
        (∫ x : ℂ, complexNormMellinIntegrand g (1 - a) x) := by
  have hswap := integral_integral_swap (f := fun (x : ℂ) (t : ℝ) => g x * ((t ^ (a - 1) * Real.exp (-(2 * Real.pi * ‖x‖ ^ 2 * t)) : ℝ) : ℂ)) (laplace_prod_integrable g hg a ha hi)
  have he (x : ℂ) (hx : x ≠ 0) :
      (∫ t : ℝ in Ioi 0, g x *
        ((t ^ (a - 1) * Real.exp (-(2 * Real.pi * ‖x‖ ^ 2 * t)) : ℝ) : ℂ)) =
      (((2 * Real.pi) ^ (-a) * Real.Gamma a : ℝ) : ℂ) *
        complexNormMellinIntegrand g (1 - a) x := by
    have hc : (∫ t : ℝ in Ioi 0,
        ((t ^ (a - 1) * Real.exp (-(2 * Real.pi * ‖x‖ ^ 2 * t)) : ℝ) : ℂ)) =
        (((∫ t : ℝ in Ioi 0,
          t ^ (a - 1) * Real.exp (-(2 * Real.pi * ‖x‖ ^ 2 * t))) : ℝ) : ℂ) :=
      integral_ofReal
    rw [integral_const_mul, hc, laplace_weight a _ ha (by positivity),
      mellin_weight a x hx]
    simp only [complexNormMellinIntegrand, if_neg hx]
    push_cast
    ring
  calc
    _ = ∫ t : ℝ in Ioi 0, ∫ x : ℂ, g x *
        ((t ^ (a - 1) * Real.exp (-(2 * Real.pi * ‖x‖ ^ 2 * t)) : ℝ) : ℂ) := by
      congr 1; ext t
      simp only [Complex.ofReal_mul, ← integral_const_mul]
      congr 1; ext x; ring
    _ = ∫ x : ℂ, ∫ t : ℝ in Ioi 0, g x *
        ((t ^ (a - 1) * Real.exp (-(2 * Real.pi * ‖x‖ ^ 2 * t)) : ℝ) : ℂ) := hswap.symm
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [(volume : Measure ℂ).ae_ne (0 : ℂ)] with x hx
      exact he x hx
lemma reciprocal_pairing_mellin (f : ℂ → ℂ) (s : ℝ) (hs : 0 < s)
    (hi : Integrable (complexNormMellinIntegrand f (1 - s)) volume)
    (hm : AEStronglyMeasurable f volume) :
    (∫ t : ℝ in Ioi 0, ((t ^ (-s) : ℝ) : ℂ) * (t : ℂ)⁻¹ *
      (∫ x : ℂ, f x * (Real.exp (-2 * Real.pi * ‖x‖ ^ 2 / t) : ℂ))) =
      (((2 * Real.pi) ^ (-s) * Real.Gamma s : ℝ) : ℂ) *
        (∫ x : ℂ, complexNormMellinIntegrand f (1 - s) x) := by
  rw [← integral_comp_rpow_Ioi (fun t : ℝ => ((t ^ (-s) : ℝ) : ℂ) * (t : ℂ)⁻¹ *
      (∫ x : ℂ, f x * (Real.exp (-2 * Real.pi * ‖x‖ ^ 2 / t) : ℂ)))
      (by norm_num : (-1 : ℝ) ≠ 0)]
  rw [← laplace_mellin f hm s hs hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [abs_neg, abs_one, one_mul, Complex.real_smul]
  rw [← Real.rpow_mul ht.le]
  have hpow : ((t ^ ((-1 : ℝ) - 1) : ℝ) : ℂ) * ((t ^ (-1 * -s) : ℝ) : ℂ) *
      ((t ^ (-1 : ℝ) : ℝ) : ℂ)⁻¹ = ((t ^ (s - 1) : ℝ) : ℂ) := by
    rw [Real.rpow_neg_one, Complex.ofReal_inv, inv_inv]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    rw [show t ^ ((-1 : ℝ) - 1) * t ^ (-1 * -s) * t =
      t ^ ((-1 : ℝ) - 1) * t ^ (-1 * -s) * t ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    ring
  rw [← mul_assoc, ← mul_assoc, hpow]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  rw [Real.rpow_neg_one, div_inv_eq_mul]
  ring

lemma gamma_ratio (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    Complex.Gammaℂ (s : ℂ) / Complex.Gammaℂ ((1 - s : ℝ) : ℂ) =
      (((2 * Real.pi) ^ (-s) * Real.Gamma s : ℝ) : ℂ) /
        (((2 * Real.pi) ^ (s - 1) * Real.Gamma (1 - s) : ℝ) : ℂ) := by
  simp only [Complex.Gammaℂ_def, Complex.Gamma_ofReal]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_neg]
  rw [show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl]
  rw [← Complex.ofReal_cpow (by positivity : 0 ≤ 2 * Real.pi),
      ← Complex.ofReal_cpow (by positivity : 0 ≤ 2 * Real.pi)]
  rw [show -(1 - s) = s - 1 by ring]
  push_cast
  have h1 : (((2 * Real.pi) ^ (s - 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by positivity : 0 < 2 * Real.pi) _).ne'
  have h2 : (Real.Gamma (1 - s) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.Gamma_pos_of_pos (by linarith : 0 < 1 - s)).ne'
  field_simp

end ComplexTateLaplace

theorem complexTraceFourier_normMellin (f : ℂ → ℂ) (hf : IsComplexAnnular f)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    complexNormMellin (complexTraceFourier f) s =
      (Complex.Gammaℂ (s : ℂ) / Complex.Gammaℂ ((1 - s : ℝ) : ℂ)) *
        complexNormMellin f (1 - s) := by
  have hfi : Integrable f volume :=
    hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
  have hfm : AEStronglyMeasurable f volume := hf.1.continuous.aestronglyMeasurable
  have hgm : AEStronglyMeasurable (complexTraceFourier f) volume := by
    have hc : Continuous (FourierTransform.fourier f) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hfi
    have he : complexTraceFourier f = fun y : ℂ =>
        2 * FourierTransform.fourier f (2 * (starRingEnd ℂ) y) := by
      funext y; exact complexTraceFourier_eq_fourier f y
    rw [he]
    exact (continuous_const.mul (hc.comp (by fun_prop))).aestronglyMeasurable
  have hgi := complexTraceFourier_normMellin_integrable f hf s hs hs1
  have hmi := complexAnnular_normMellin_integrable f hf s hs hs1
  have hL := ComplexTateLaplace.laplace_mellin (complexTraceFourier f) hgm
    (1 - s) (by linarith) (by simpa using hgi)
  have hR := ComplexTateLaplace.reciprocal_pairing_mellin f s hs hmi hfm
  have hEq : (((2 * Real.pi) ^ (s - 1) * Real.Gamma (1 - s) : ℝ) : ℂ) *
      (∫ y : ℂ, complexNormMellinIntegrand (complexTraceFourier f) s y) =
      (((2 * Real.pi) ^ (-s) * Real.Gamma s : ℝ) : ℂ) *
        (∫ x : ℂ, complexNormMellinIntegrand f (1 - s) x) := by
    rw [← hR]
    rw [show -(1 - s) = s - 1 by ring,
      show 1 - (1 - s) = s by ring,
      show (1 - s) - 1 = -s by ring] at hL
    rw [← hL]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    have he : (fun x : ℂ => complexTraceFourier f x *
        (Real.exp (-(2 * Real.pi * ‖x‖ ^ 2 * t)) : ℂ)) =
        (fun x : ℂ => complexTraceFourier f x *
        (Real.exp (-2 * Real.pi * t * ‖x‖ ^ 2) : ℂ)) := by
      funext x; congr 2; ring
    rw [he, complexTraceFourier_gaussian_pairing f hf t ht]
    ring
  have hC : (((2 * Real.pi) ^ (s - 1) * Real.Gamma (1 - s) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (Real.rpow_pos_of_pos (by positivity : 0 < 2 * Real.pi) _)
      (Real.Gamma_pos_of_pos (by linarith : 0 < 1 - s))).ne'
  rw [ComplexTateLaplace.gamma_ratio s hs hs1, complexNormMellin, complexNormMellin]
  have hEq' : (∫ y : ℂ, complexNormMellinIntegrand (complexTraceFourier f) s y) =
      ((((2 * Real.pi) ^ (-s) * Real.Gamma s : ℝ) : ℂ) *
        (∫ x : ℂ, complexNormMellinIntegrand f (1 - s) x)) /
        (((2 * Real.pi) ^ (s - 1) * Real.Gamma (1 - s) : ℝ) : ℂ) :=
    (eq_div_iff hC).mpr (by rw [mul_comm]; exact hEq)
  rw [hEq']
  ring

theorem complexGamma_ratio_ne_zero (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    Complex.Gammaℂ (s : ℂ) / Complex.Gammaℂ ((1 - s : ℝ) : ℂ) ≠ 0 := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  apply div_ne_zero
  · exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)))
      (Complex.Gamma_ne_zero_of_re_pos (by simpa using hs))
  · exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)))
      (Complex.Gamma_ne_zero_of_re_pos (by simpa using sub_pos.mpr hs1))

end
end DedekindZetaZeroFree
