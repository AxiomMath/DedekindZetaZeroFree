module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.PositiveIntertwinerChartEstimates

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPReferenceChange.StandardComplexImage.FamilyCorrect
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxHarmonicIntertwinerSpectrum
open MeasureTheory Filter

def height (g : ComplexGL2) : ℝ :=
  (‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ / bottomRowNormSq g) ^ 2

def twist (s : ℂ) (g : ComplexGL2) : ℂ :=
  Complex.exp (s * (Real.log (height g) : ℂ))

def plusValue (f : PrincipalSeries positiveParameter) (s : ℂ) (g : ComplexGL2) : ℂ :=
  twist s g * f g

def chamber : Set ℂ := {s | (-1 / 6 : ℝ) < s.re}

theorem height_pos (g : ComplexGL2) : 0 < height g := by
  have hb := bottom_pos g
  have hd : 0 < ‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ :=
    norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero
  exact pow_pos (div_pos hd hb) _

@[simp] theorem twist_zero (g : ComplexGL2) : twist 0 g = 1 := by
  simp [twist]

@[simp] theorem plusValue_zero (f : PrincipalSeries positiveParameter) (g : ComplexGL2) :
    plusValue f 0 g = f g := by
  simp [plusValue]

theorem height_upperTriangular (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    height (upperTriangular a d b * g) = complexAbs ((a : ℂ) / (d : ℂ)) * height g := by
  have hb : bottomRowNormSq (upperTriangular a d b * g) =
      ‖(d : ℂ)‖ ^ 2 * bottomRowNormSq g := by
    simp [bottomRowNormSq, upperTriangular, Matrix.mul_apply, Fin.sum_univ_two,
      norm_mul, mul_pow]
    ring
  have hd : ‖((Matrix.GeneralLinearGroup.det (upperTriangular a d b * g) : ℂˣ) : ℂ)‖ =
      ‖(a : ℂ)‖ * ‖(d : ℂ)‖ * ‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ := by
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_mul, upperTriangular,
      Matrix.det_fin_two, norm_mul]
  have hdn : ‖(d : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr d.ne_zero
  simp only [height, hb, hd, complexAbs, norm_div]
  field_simp [hdn, (bottom_pos g).ne']
  <;> ring

theorem twist_upperTriangular (s : ℂ) (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    twist s (upperTriangular a d b * g) =
      Complex.exp (s * (Real.log (complexAbs ((a : ℂ) / (d : ℂ))) : ℂ)) * twist s g := by
  have ha : 0 < complexAbs ((a : ℂ) / (d : ℂ)) := by
    unfold complexAbs
    exact pow_pos (norm_pos_iff.mpr (div_ne_zero a.ne_zero d.ne_zero)) _
  rw [twist, height_upperTriangular, Real.log_mul ha.ne' (height_pos g).ne']
  simp only [Complex.ofReal_add, mul_add, Complex.exp_add, twist]

theorem plusValue_covariance (f : PrincipalSeries positiveParameter) (s : ℂ)
    (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    plusValue f s (upperTriangular a d b * g) =
      ((inductionWeight positiveParameter a d : ℂ) *
        Complex.exp (s * (Real.log (complexAbs ((a : ℂ) / (d : ℂ))) : ℂ))) *
          plusValue f s g := by
  rw [plusValue, twist_upperTriangular, f.property.1]
  unfold plusValue
  ring

theorem height_open (z : ℂ) :
    height (weyl * upperUnipotent z) = (1 + ‖z‖ ^ 2)⁻¹ ^ 2 := by
  simp [height, bottomRowNormSq, weyl, upperUnipotent,
    Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_mul, Matrix.det_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]

theorem height_infinity (z : ℂ) :
    height (lowerUnipotent z) = (1 + ‖z‖ ^ 2)⁻¹ ^ 2 := by
  simp [height, bottomRowNormSq, lowerUnipotent,
    Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, add_comm]

theorem twist_chart_smooth (s : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ =>
      Complex.exp (s * (Real.log ((1 + ‖z‖ ^ 2)⁻¹ ^ 2) : ℂ))) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => 1 + ‖z‖ ^ 2) := by
    simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    exact contDiff_const.add ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff))
  have hh := (hc.inv (by intro z; positivity)).pow 2
  have hl := hh.log (by
    intro z
    exact pow_ne_zero 2 (inv_ne_zero (by positivity : (1 + ‖z‖ ^ 2 : ℝ) ≠ 0)))
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hl)).cexp

theorem plusValue_charts_smooth (f : PrincipalSeries positiveParameter) (s : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (openCoordinate (plusValue f s)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (infinityCoordinate (plusValue f s)) := by
  have ho : openCoordinate (plusValue f s) = fun z =>
      Complex.exp (s * (Real.log ((1 + ‖z‖ ^ 2)⁻¹ ^ 2) : ℂ)) * openCoordinate f z := by
    funext z
    simp only [openCoordinate, plusValue, twist, height_open]
  have hi : infinityCoordinate (plusValue f s) = fun z =>
      Complex.exp (s * (Real.log ((1 + ‖z‖ ^ 2)⁻¹ ^ 2) : ℂ)) * infinityCoordinate f z := by
    funext z
    simp only [infinityCoordinate, plusValue, twist, height_infinity]
  rw [ho, hi]
  exact ⟨(twist_chart_smooth s).mul f.property.2.1,
    (twist_chart_smooth s).mul f.property.2.2⟩

def realTwisted (f : PrincipalSeries positiveParameter) (r : ℝ) :
    PrincipalSeries (positiveParameter + r) := by
  refine ⟨plusValue f (r : ℂ), ?_, (plusValue_charts_smooth f (r : ℂ)).1,
    (plusValue_charts_smooth f (r : ℂ)).2⟩
  intro a d b g
  rw [plusValue_covariance]
  congr 1
  have hp : 0 < complexAbs ((a : ℂ) / (d : ℂ)) := by
    exact pow_pos (norm_pos_iff.mpr (div_ne_zero a.ne_zero d.ne_zero)) _
  change (((complexAbs ((a : ℂ) / (d : ℂ))) ^ (1 / 2 + positiveParameter) : ℝ) : ℂ) *
    Complex.exp ((r : ℂ) * (Real.log (complexAbs ((a : ℂ) / (d : ℂ))) : ℂ)) =
    (((complexAbs ((a : ℂ) / (d : ℂ))) ^ (1 / 2 + (positiveParameter + r)) : ℝ) : ℂ)
  simp only [Real.rpow_def_of_pos hp, Complex.ofReal_exp]
  rw [← Complex.ofReal_mul, ← Complex.exp_add, ← Complex.ofReal_add]
  congr 1
  push_cast
  ring

@[simp] theorem norm_plusValue (f : PrincipalSeries positiveParameter) (s : ℂ)
    (g : ComplexGL2) : ‖plusValue f s g‖ = ‖realTwisted f s.re g‖ := by
  simp only [plusValue, twist, realTwisted, norm_mul, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private theorem transition_norm (r : ℝ) (f : PrincipalSeries r) (x : ℂ)
    (hx : 1 ≤ ‖x‖) :
    ‖openCoordinate f x‖ = ‖x‖ ^ (-2 * (1 + 2 * r)) *
      ‖infinityCoordinate f x⁻¹‖ := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx; norm_num at hx
  have h := coordinate_transition r f x⁻¹ (inv_ne_zero hx0)
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hw : transitionWeight r x⁻¹ = ‖x‖ ^ (2 * (1 + 2 * r)) := by
    simp only [transitionWeight, norm_inv, Real.rpow_eq_pow]
    rw [Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)]
    congr 1
    ring
  rw [inv_inv, hw] at h
  have hn := congrArg norm h
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hxp _)] at hn
  have hr : ‖x‖ ^ (-2 * (1 + 2 * r)) * ‖x‖ ^ (2 * (1 + 2 * r)) = 1 := by
    rw [← Real.rpow_add hxp]; simp
  rw [hn, ← mul_assoc, hr, one_mul]

theorem openCoordinate_envelope (r : ℝ) (hr : 0 < r) (f : PrincipalSeries r) (x : ℂ) :
    ‖openCoordinate f x‖ ≤ (2 : ℝ) ^ (2 * (1 + 2 * r)) * chartSeminorm r 0 f *
      (1 + ‖x‖) ^ (-2 * (1 + 2 * r)) := by
  have hs : 0 ≤ chartSeminorm r 0 f := apply_nonneg _ _
  have ht : -2 * (1 + 2 * r) ≤ 0 := by linarith
  by_cases hx : 1 ≤ ‖x‖
  · have hxi : x⁻¹ ∈ Metric.closedBall (0 : ℂ) 1 := by
      simp only [Metric.mem_closedBall, dist_zero_right, norm_inv]
      exact inv_le_one_of_one_le₀ hx
    have hi := infinityCoordinate_norm_le_chartSeminorm_zero r f x⁻¹ hxi
    have hp : ‖x‖ ^ (-2 * (1 + 2 * r)) ≤
        (2 : ℝ) ^ (2 * (1 + 2 * r)) * (1 + ‖x‖) ^ (-2 * (1 + 2 * r)) := by
      have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1 + ‖x‖) / 2)
        (by linarith : (1 + ‖x‖) / 2 ≤ ‖x‖) ht
      rw [Real.div_rpow (by positivity) (by positivity)] at h
      have hn : -2 * (1 + 2 * r) = -(2 * (1 + 2 * r)) := by ring
      rw [hn, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul] at h
      rw [hn]
      simpa only [mul_comm] using h
    rw [transition_norm r f x hx]
    calc
      _ ≤ ‖x‖ ^ (-2 * (1 + 2 * r)) * chartSeminorm r 0 f :=
        mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ ((2 : ℝ) ^ (2 * (1 + 2 * r)) * (1 + ‖x‖) ^ (-2 * (1 + 2 * r))) *
          chartSeminorm r 0 f := mul_le_mul_of_nonneg_right hp hs
      _ = _ := by ring
  · have hball : x ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using (le_of_not_ge hx)
    have ho := openCoordinate_norm_le_chartSeminorm_zero r f x hball
    have hw : 1 ≤ (2 : ℝ) ^ (2 * (1 + 2 * r)) * (1 + ‖x‖) ^ (-2 * (1 + 2 * r)) := by
      have h := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < 1 + ‖x‖)
        (by linarith [le_of_not_ge hx] : 1 + ‖x‖ ≤ (2 : ℝ)) ht
      have he : (2 : ℝ) ^ (2 * (1 + 2 * r)) * (2 : ℝ) ^ (-2 * (1 + 2 * r)) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      calc
        1 = (2 : ℝ) ^ (2 * (1 + 2 * r)) * (2 : ℝ) ^ (-2 * (1 + 2 * r)) := he.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num) _)
    calc
      ‖openCoordinate f x‖ ≤ chartSeminorm r 0 f := ho
      _ = 1 * chartSeminorm r 0 f := by ring
      _ ≤ ((2 : ℝ) ^ (2 * (1 + 2 * r)) * (1 + ‖x‖) ^ (-2 * (1 + 2 * r))) *
          chartSeminorm r 0 f := mul_le_mul_of_nonneg_right hw hs
      _ = _ := by ring

theorem real_intertwiner_integrable (β : ℂˣ) (r : ℝ) (hr : 0 < r)
    (f : PrincipalSeries r) (g : ComplexGL2) :
    Integrable (fun x : ℂ => f (weyl * upperUnipotent x * g)) (characterHaar β) := by
  letI := characterHaar_isAddHaarMeasure β
  let F := KPCplxPrincipalSeriesCharts.rightTranslate r g f
  change Integrable (openCoordinate F) (characterHaar β)
  have hw : Integrable (fun x : ℂ => (1 + ‖x‖) ^ (-2 * (1 + 2 * r)))
      (characterHaar β) := by
    rw [show -2 * (1 + 2 * r) = -(2 * (1 + 2 * r)) by ring]
    apply integrable_one_add_norm
    simp only [Complex.finrank_real_complex]
    norm_num
    linarith
  exact (hw.const_mul ((2 : ℝ) ^ (2 * (1 + 2 * r)) * chartSeminorm r 0 F)).mono'
    F.property.2.1.continuous.aestronglyMeasurable
    (Eventually.of_forall (openCoordinate_envelope r hr F))

private theorem height_orbit_continuous (g : ComplexGL2) :
    Continuous (fun x : ℂ => height (weyl * upperUnipotent x * g)) := by
  have he : (fun x : ℂ => height (weyl * upperUnipotent x * g)) = fun x =>
      (‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ /
        (‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + x * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
         ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + x * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2)) ^ 2 := by
    funext x
    simp [height, bottomRowNormSq, weyl, upperUnipotent,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_mul, Matrix.det_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, norm_sub_rev]
  rw [he]
  apply Continuous.pow
  apply Continuous.div continuous_const
  · fun_prop
  · intro x
    have hb := bottom_pos (weyl * upperUnipotent x * g)
    simpa [bottomRowNormSq, weyl, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
      using hb.ne'

private theorem plusValue_orbit_continuous (f : PrincipalSeries positiveParameter)
    (s : ℂ) (g : ComplexGL2) :
    Continuous (fun x : ℂ => plusValue f s (weyl * upperUnipotent x * g)) := by
  unfold plusValue twist
  apply Continuous.mul
  · exact (continuous_const.mul (Complex.continuous_ofReal.comp
      ((height_orbit_continuous g).log (fun x => (height_pos _).ne')))).cexp
  · exact (KPCplxPrincipalSeriesCharts.rightTranslate positiveParameter g f).property.2.1.continuous

theorem chamber_integrable (β : ℂˣ) (s : ℂ) (hs : s ∈ chamber)
    (f : PrincipalSeries positiveParameter) (g : ComplexGL2) :
    Integrable (fun x : ℂ => plusValue f s (weyl * upperUnipotent x * g)) (characterHaar β) := by
  have hr : 0 < positiveParameter + s.re := by
    change -1 / 6 < s.re at hs
    change 0 < 1 / 6 + s.re
    linarith
  exact ((real_intertwiner_integrable β _ hr (realTwisted f s.re) g).norm).mono'
    (plusValue_orbit_continuous f s g).aestronglyMeasurable
    (Eventually.of_forall (fun x => (norm_plusValue f s _).le))

end DedekindZetaZeroFree.KPReferenceChange.StandardComplexImage.FamilyCorrect
