module

public import DedekindZetaZeroFree.Theta.Profiles.ReciprocalGammaStripBounds
public import DedekindZetaZeroFree.Analysis.VerticalContourShift

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/Mellin/VerticalContourShift.lean.
Source: InverseContour.lean.
-/

namespace DedekindZetaZeroFree
noncomputable section

attribute [-instance] instCommCStarAlgebraComplex
attribute [local instance 2000] Complex.instNormedField Complex.instNormedAddCommGroup
attribute [local instance 2100] NonUnitalSeminormedRing.toSeminormedAddCommGroup

def thetaProfileGaussianContourIntegrand
    (C₀ A₀ : ℝ) (r : ℕ) (σ T t : ℝ) : ℂ :=
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  Complex.exp (s ^ 2) * thetaProfileReciprocalMellinFactor C₀ A₀ r s *
    (T : ℂ) ^ s

def thetaProfileGaussianContour
    (C₀ A₀ : ℝ) (r : ℕ) (σ T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) •
    ∫ t : ℝ, thetaProfileGaussianContourIntegrand C₀ A₀ r σ T t

def thetaProfileGaussianKernel (C₀ A₀ : ℝ) (r : ℕ) (T : ℝ) : ℂ :=
  thetaProfileGaussianContour C₀ A₀ r 0 T

private theorem gaussianContour_bound
    (C₀ A₀ : ℝ) (r : ℕ) (hC₀ : 0 < C₀) (hA₀ : 0 < A₀) (hr : 1 ≤ r)
    (σ : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ T : ℝ, 0 < T → ∀ t : ℝ,
      ‖thetaProfileGaussianContourIntegrand C₀ A₀ r σ T t‖ ≤
        (D * Real.rpow T σ) * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := thetaProfileReciprocalMellinFactor_strip_exp_bound
    C₀ A₀ r hC₀ hA₀ hr σ σ le_rfl
  let k : ℝ := 2 * Real.pi * (r : ℝ)
  refine ⟨C * Real.exp (σ ^ 2 + k ^ 2 / 2), by positivity, ?_⟩
  intro T hT t
  have hs : (((σ : ℂ) + (t : ℂ) * Complex.I) ^ 2).re = σ ^ 2 - t ^ 2 := by
    simp [pow_two, Complex.mul_re, Complex.add_re, Complex.mul_im]
  have hR := hb ((σ : ℂ) + (t : ℂ) * Complex.I) (by simp) (by simp)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hR
  have he : σ ^ 2 - t ^ 2 + k * |t| ≤ σ ^ 2 + k ^ 2 / 2 - t ^ 2 / 2 := by
    nlinarith [sq_nonneg (|t| - k), sq_abs t]
  simp only [thetaProfileGaussianContourIntegrand, norm_mul, Complex.norm_exp, hs]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hT]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ (Real.exp (σ ^ 2 - t ^ 2) * (C * Real.exp (k * |t|))) * T ^ σ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hR (Real.exp_nonneg _)) (Real.rpow_nonneg hT.le _)
    _ = C * Real.exp (σ ^ 2 - t ^ 2 + k * |t|) * T ^ σ := by
      rw [Real.exp_add]; ring
    _ ≤ C * Real.exp (σ ^ 2 + k ^ 2 / 2 - t ^ 2 / 2) * T ^ σ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC.le)
        (Real.rpow_nonneg hT.le _)
    _ = _ := by
      rw [show σ ^ 2 + k ^ 2 / 2 - t ^ 2 / 2 =
        (σ ^ 2 + k ^ 2 / 2) + (-(1 / 2 : ℝ) * t ^ 2) by ring, Real.exp_add]
      simp only [Real.rpow_eq_pow]
      ring

private theorem gaussianContour_continuous_line
    (C₀ A₀ : ℝ) (r : ℕ) (hC₀ : 0 < C₀) (hA₀ : 0 < A₀) (hr : 1 ≤ r)
    (σ T : ℝ) (hT : 0 < T) :
    Continuous (thetaProfileGaussianContourIntegrand C₀ A₀ r σ T) := by
  have hs : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  exact ((Complex.continuous_exp.comp (hs.pow 2)).mul
    ((thetaProfileReciprocalMellinFactor_differentiable C₀ A₀ r hC₀ hA₀ hr).continuous.comp hs)).mul
    ((differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hT.ne'))).continuous.comp hs)

theorem thetaProfileGaussianContour_integrable
    (C₀ A₀ : ℝ) (r : ℕ) (hC₀ : 0 < C₀) (hA₀ : 0 < A₀) (hr : 1 ≤ r)
    (σ T : ℝ) (hT : 0 < T) :
    MeasureTheory.Integrable
      (thetaProfileGaussianContourIntegrand C₀ A₀ r σ T) := by
  obtain ⟨D, hD, hb⟩ := gaussianContour_bound C₀ A₀ r hC₀ hA₀ hr σ
  exact ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
    (D * Real.rpow T σ)).mono'
    (gaussianContour_continuous_line C₀ A₀ r hC₀ hA₀ hr σ T hT).aestronglyMeasurable
    (Filter.Eventually.of_forall (hb T hT))

private theorem gaussian_polynomial_decay (t : ℝ) :
    Real.exp (-(1 / 2 : ℝ) * t ^ 2) ≤ 4 * (1 + |t|) ^ (-2 : ℝ) := by
  have he := Real.add_one_le_exp (t ^ 2 / 2)
  have hp : (1 + |t|) ^ 2 ≤ 4 * Real.exp (t ^ 2 / 2) := by
    nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |t|), Real.rpow_two]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (1 + |t|) ^ 2)).mpr
  have hn : Real.exp (-(1 / 2 : ℝ) * t ^ 2) * Real.exp (t ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  nlinarith [mul_le_mul_of_nonneg_left hp (Real.exp_nonneg (-(1 / 2 : ℝ) * t ^ 2))]

private theorem gaussianContour_strip_decay
    (C₀ A₀ : ℝ) (r : ℕ) (hC₀ : 0 < C₀) (hA₀ : 0 < A₀) (hr : 1 ≤ r)
    (a b T : ℝ) (hab : a ≤ b) (hT : 0 < T) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s ∈ comparisonClosedStrip a b,
      ‖Complex.exp (s ^ 2) * thetaProfileReciprocalMellinFactor C₀ A₀ r s *
        (T : ℂ) ^ s‖ ≤ D * (1 + |s.im|) ^ (-2 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := thetaProfileReciprocalMellinFactor_strip_exp_bound
    C₀ A₀ r hC₀ hA₀ hr a b hab
  let m : ℝ := |a| + |b|
  let k : ℝ := 2 * Real.pi * (r : ℝ)
  let D : ℝ := C * Real.exp (m ^ 2 + k ^ 2 / 2 + m * |Real.log T|)
  refine ⟨4 * D, by dsimp [D]; positivity, ?_⟩
  intro s hs
  have hm : |s.re| ≤ m := by
    apply abs_le.mpr
    constructor
    · have := neg_abs_le a
      dsimp [m]
      linarith [hs.1, abs_nonneg b]
    · have := le_abs_self b
      dsimp [m]
      linarith [hs.2, abs_nonneg a]
  have hsq : s.re ^ 2 ≤ m ^ 2 := by
    have hm0 : 0 ≤ m := by dsimp [m]; positivity
    nlinarith [sq_abs s.re, mul_nonneg (sub_nonneg.mpr hm)
      (add_nonneg hm0 (abs_nonneg s.re))]
  have hlog : Real.log T * s.re ≤ m * |Real.log T| := by
    calc
      _ ≤ |Real.log T * s.re| := le_abs_self _
      _ = |s.re| * |Real.log T| := by rw [abs_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right hm (abs_nonneg _)
  have he : s.re ^ 2 - s.im ^ 2 + k * |s.im| + Real.log T * s.re ≤
      m ^ 2 + k ^ 2 / 2 + m * |Real.log T| - s.im ^ 2 / 2 := by
    nlinarith [sq_nonneg (|s.im| - k), sq_abs s.im]
  have hg : ‖Complex.exp (s ^ 2) * thetaProfileReciprocalMellinFactor C₀ A₀ r s *
      (T : ℂ) ^ s‖ ≤ D * Real.exp (-(1 / 2 : ℝ) * s.im ^ 2) := by
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hT,
      Real.rpow_def_of_pos hT]
    have hsre : (s ^ 2).re = s.re ^ 2 - s.im ^ 2 := by
      simp [pow_two, Complex.mul_re]
    rw [hsre]
    calc
      _ ≤ Real.exp (s.re ^ 2 - s.im ^ 2) * (C * Real.exp (k * |s.im|)) *
          Real.exp (Real.log T * s.re) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hb s hs.1 hs.2) (Real.exp_nonneg _))
          (Real.exp_nonneg _)
      _ = C * Real.exp (s.re ^ 2 - s.im ^ 2 + k * |s.im| + Real.log T * s.re) := by
        rw [Real.exp_add, Real.exp_add]; ring
      _ ≤ C * Real.exp (m ^ 2 + k ^ 2 / 2 + m * |Real.log T| - s.im ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC.le
      _ = _ := by
        dsimp [D]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hD : 0 ≤ D := by dsimp [D]; positivity
  calc
    _ ≤ D * Real.exp (-(1 / 2 : ℝ) * s.im ^ 2) := hg
    _ ≤ D * (4 * (1 + |s.im|) ^ (-2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (gaussian_polynomial_decay s.im) hD
    _ = _ := by ring

theorem thetaProfileGaussianContour_eq_kernel
    (C₀ A₀ : ℝ) (r : ℕ) (hC₀ : 0 < C₀) (hA₀ : 0 < A₀) (hr : 1 ≤ r)
    (σ T : ℝ) (hT : 0 < T) :
    thetaProfileGaussianContour C₀ A₀ r σ T =
      thetaProfileGaussianKernel C₀ A₀ r T := by
  let f : ℂ → ℂ := fun s => Complex.exp (s ^ 2) *
    thetaProfileReciprocalMellinFactor C₀ A₀ r s * (T : ℂ) ^ s
  have hf : Differentiable ℂ f :=
    ((Complex.differentiable_exp.comp (differentiable_id.pow 2)).mul
      (thetaProfileReciprocalMellinFactor_differentiable C₀ A₀ r hC₀ hA₀ hr)).mul
      (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hT.ne')))
  have he (a b : ℝ) (hab : a < b) :
      (∫ t : ℝ, thetaProfileGaussianContourIntegrand C₀ A₀ r a T t) =
      ∫ t : ℝ, thetaProfileGaussianContourIntegrand C₀ A₀ r b T t := by
    obtain ⟨D, hD, hb⟩ := gaussianContour_strip_decay C₀ A₀ r hC₀ hA₀ hr a b T hab.le hT
    exact verticalIntegral_eq_of_strip_decay a b D f Set.univ hab hD
      isOpen_univ (Set.subset_univ _) hf.differentiableOn hb
  unfold thetaProfileGaussianKernel thetaProfileGaussianContour
  congr 1
  rcases lt_trichotomy σ 0 with hσ | hσ | hσ
  · exact he σ 0 hσ
  · rw [hσ]
  · exact (he 0 σ hσ).symm

theorem thetaProfileGaussianKernel_continuousOn
    (C₀ A₀ : ℝ) (r : ℕ) (hC₀ : 0 < C₀) (hA₀ : 0 < A₀) (hr : 1 ≤ r) :
    ContinuousOn (thetaProfileGaussianKernel C₀ A₀ r) (Set.Ioi (0 : ℝ)) := by
  obtain ⟨D, hD, hb⟩ := gaussianContour_bound C₀ A₀ r hC₀ hA₀ hr 0
  have hi : ContinuousOn
      (fun T : ℝ => ∫ t : ℝ, thetaProfileGaussianContourIntegrand C₀ A₀ r 0 T t)
      (Set.Ioi (0 : ℝ)) := by
    apply MeasureTheory.continuousOn_of_dominated
      (bound := fun t : ℝ => D * Real.exp (-(1 / 2 : ℝ) * t ^ 2))
    · intro T hT
      exact (gaussianContour_continuous_line C₀ A₀ r hC₀ hA₀ hr 0 T hT).aestronglyMeasurable
    · intro T hT
      exact Filter.Eventually.of_forall (fun t => by simpa [Real.rpow_zero] using hb T hT t)
    · exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul D
    · apply Filter.Eventually.of_forall
      intro t
      have hp : ContinuousOn (fun T : ℝ => (T : ℂ) ^ ((0 : ℂ) + (t : ℂ) * Complex.I))
          (Set.Ioi (0 : ℝ)) :=
        Complex.continuous_ofReal.continuousOn.cpow_const
          (fun T hT => Complex.ofReal_mem_slitPlane.mpr hT)
      exact continuousOn_const.mul hp
  change ContinuousOn (fun T : ℝ => (1 / (2 * Real.pi) : ℝ) •
    ∫ t : ℝ, thetaProfileGaussianContourIntegrand C₀ A₀ r 0 T t) (Set.Ioi 0)
  exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 / (2 * Real.pi) : ℝ))
    (Set.Ioi 0)).smul hi

private theorem gaussianKernel_power_bound
    (C₀ A₀ : ℝ) (r : ℕ) (hC₀ : 0 < C₀) (hA₀ : 0 < A₀) (hr : 1 ≤ r)
    (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T →
      ‖thetaProfileGaussianKernel C₀ A₀ r T‖ ≤ C * Real.rpow T a := by
  obtain ⟨D, hD, hb⟩ := gaussianContour_bound C₀ A₀ r hC₀ hA₀ hr a
  let J : ℝ := ∫ t : ℝ, Real.exp (-(1 / 2 : ℝ) * t ^ 2)
  have hJ : 0 ≤ J := MeasureTheory.integral_nonneg (fun t => (Real.exp_pos _).le)
  let B : ℝ := (1 / (2 * Real.pi)) * D * J
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B + 1, by linarith, ?_⟩
  intro T hT
  have hg := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  have hmono := MeasureTheory.integral_mono
    (thetaProfileGaussianContour_integrable C₀ A₀ r hC₀ hA₀ hr a T hT).norm
    (hg.const_mul (D * Real.rpow T a)) (hb T hT)
  rw [MeasureTheory.integral_const_mul] at hmono
  rw [← thetaProfileGaussianContour_eq_kernel C₀ A₀ r hC₀ hA₀ hr a T hT]
  simp only [thetaProfileGaussianContour, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((D * Real.rpow T a) * J) :=
      mul_le_mul_of_nonneg_left
        ((MeasureTheory.norm_integral_le_integral_norm _).trans hmono) (by positivity)
    _ = B * Real.rpow T a := by dsimp [B]; ring
    _ ≤ (B + 1) * Real.rpow T a :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hT.le _)

set_option maxHeartbeats 800000 in

theorem thetaProfileGaussianKernel_absolute_moment
    (C₀ A₀ : ℝ) (r : ℕ) (hC₀ : 0 < C₀) (hA₀ : 0 < A₀) (hr : 1 ≤ r)
    (a : ℝ) :
    MeasureTheory.IntegrableOn
      (fun T : ℝ => ‖thetaProfileGaussianKernel C₀ A₀ r T‖ * Real.rpow T a / T)
      (Set.Ioi (0 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := gaussianKernel_power_bound C₀ A₀ r hC₀ hA₀ hr (1 - a)
  obtain ⟨D, hD, hd⟩ := gaussianKernel_power_bound C₀ A₀ r hC₀ hA₀ hr (-1 - a)
  let f : ℝ → ℝ := fun T => ‖thetaProfileGaussianKernel C₀ A₀ r T‖ * Real.rpow T a / T
  have hc : ContinuousOn f (Set.Ioi (0 : ℝ)) := by
    apply ((thetaProfileGaussianKernel_continuousOn C₀ A₀ r hC₀ hA₀ hr).norm.mul
      (continuousOn_id.rpow_const (fun T hT => Or.inl (ne_of_gt hT)))).div
      continuousOn_id (fun T hT => ne_of_gt hT)
  have hbound (p E T : ℝ) (hT : 0 < T)
      (h : ‖thetaProfileGaussianKernel C₀ A₀ r T‖ ≤ E * Real.rpow T p) :
      ‖f T‖ ≤ E * T ^ (p + a - 1) := by
    have hn : 0 ≤ f T := by dsimp [f]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    calc
      f T ≤ (E * Real.rpow T p) * Real.rpow T a / T :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hT.le _)) hT.le
      _ = E * T ^ (p + a - 1) := by
        rw [Real.rpow_eq_pow, Real.rpow_eq_pow, Real.rpow_sub hT, Real.rpow_one,
          Real.rpow_add hT]
        ring
  have hsmall : MeasureTheory.IntegrableOn f (Set.Ioc (0 : ℝ) 1) := by
    have hg : MeasureTheory.IntegrableOn (fun _ : ℝ => C) (Set.Ioc (0 : ℝ) 1) :=
      MeasureTheory.integrableOn_const (by simp)
    apply hg.mono' ((hc.mono (fun T (hT : T ∈ Set.Ioc (0 : ℝ) 1) => hT.1)).aestronglyMeasurable
      measurableSet_Ioc)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with T hT
    simpa only [show 1 - a + a - 1 = (0 : ℝ) by ring, Real.rpow_zero, mul_one]
      using hbound (1 - a) C T hT.1 (hb T hT.1)
  have hlarge : MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ)) := by
    have hg := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul D
    apply hg.mono' ((hc.mono (fun T (hT : T ∈ Set.Ioi (1 : ℝ)) => (show (0 : ℝ) < T from lt_trans (by norm_num) hT))).aestronglyMeasurable
      measurableSet_Ioi)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with T hT
    simpa only [show -1 - a + a - 1 = (-2 : ℝ) by ring]
      using hbound (-1 - a) D T (lt_trans zero_lt_one hT) (hd T (lt_trans zero_lt_one hT))
  have hu := MeasureTheory.integrableOn_union.mpr ⟨hsmall, hlarge⟩
  simpa only [Set.Ioc_union_Ioi (show (1 : ℝ) ≤ max 0 1 by norm_num),
    min_eq_left zero_le_one] using hu

theorem thetaProfileGaussianKernel_rpow_bound
    (C₀ A₀ : ℝ) (r : ℕ) (hC₀ : 0 < C₀) (hA₀ : 0 < A₀) (hr : 1 ≤ r)
    (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T →
      ‖thetaProfileGaussianKernel C₀ A₀ r T‖ ≤ C * Real.rpow T a := by
  exact gaussianKernel_power_bound C₀ A₀ r hC₀ hA₀ hr a

end
end DedekindZetaZeroFree
