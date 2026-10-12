module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.ComplexIntertwinerImageAndHarmonicExtraction

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxJacquetFunctional

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage MeasureTheory
open scoped Topology

private theorem upperUnipotent_mul (x t : ℂ) :
    upperUnipotent x * upperUnipotent t = upperUnipotent (x + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent] <;> ring

private theorem weyl_upperUnipotent_mul (x t : ℂ) :
    weyl * upperUnipotent x * upperUnipotent t = weyl * upperUnipotent (x + t) := by
  rw [mul_assoc, upperUnipotent_mul]

noncomputable def jacquetIntegral (β : ℂˣ)
    (f : PrincipalSeries positiveParameter) : ℂ :=
  ∫ x : ℂ, f (weyl * upperUnipotent x) * (character (β : ℂ) (-x) : ℂ)
    ∂characterHaar β

theorem jacquetIntegral_integrable (β : ℂˣ) (f : PrincipalSeries positiveParameter) :
    Integrable (fun x : ℂ =>
      f (weyl * upperUnipotent x) * (character (β : ℂ) (-x) : ℂ)) (characterHaar β) := by
  have h := (KPCplxIntertwinerEigenvalues.intertwinerIntegral_exists β f).1 1
  simp only [mul_one] at h
  refine h.mul_bdd (c := 1) ?_ ?_
  · have hcont : Continuous (fun x : ℂ => (character (β : ℂ) (-x) : ℂ)) := by
      refine continuous_subtype_val.comp ?_
      show Continuous (fun x : ℂ => Circle.exp (((β : ℂ) * (-x)).re))
      exact Circle.exp.continuous.comp (by fun_prop)
    exact hcont.aestronglyMeasurable
  · filter_upwards with x
    rw [Circle.norm_coe]

noncomputable def jacquetLinearMap (β : ℂˣ) :
    PrincipalSeries positiveParameter →ₗ[ℂ] ℂ where
  toFun := jacquetIntegral β
  map_add' f h := by
    change (∫ x : ℂ, (f (weyl * upperUnipotent x) + h (weyl * upperUnipotent x)) *
      (character (β : ℂ) (-x) : ℂ) ∂characterHaar β) = _
    simp only [add_mul]
    exact integral_add (jacquetIntegral_integrable β f) (jacquetIntegral_integrable β h)
  map_smul' c f := by
    change (∫ x : ℂ, (c * f (weyl * upperUnipotent x)) *
      (character (β : ℂ) (-x) : ℂ) ∂characterHaar β) = c * jacquetIntegral β f
    simp only [mul_assoc]
    exact integral_smul c (fun x : ℂ =>
      f (weyl * upperUnipotent x) * (character (β : ℂ) (-x) : ℂ))

private theorem chart_zero_bound (s : ℝ) (f : PrincipalSeries s) (x : ℂ)
    (hx : ‖x‖ ≤ 1) :
    ‖openCoordinate f x‖ ≤ chartSeminorm s 0 f ∧
      ‖infinityCoordinate f x‖ ≤ chartSeminorm s 0 f := by
  have hmem : x ∈ Metric.closedBall (0 : ℂ) 1 := by simpa using hx
  have h1 := (isCompact_closedBall (0 : ℂ) 1).bddAbove_image
    (f.property.2.1.continuous.norm.continuousOn)
  have h2 := (isCompact_closedBall (0 : ℂ) 1).bddAbove_image
    (f.property.2.2.continuous.norm.continuousOn)
  change _ ≤ max _ _ ∧ _ ≤ max _ _
  simp only [norm_iteratedFDeriv_zero]
  exact ⟨(le_csSup h1 ⟨x, hmem, rfl⟩).trans (le_max_left _ _),
    (le_csSup h2 ⟨x, hmem, rfl⟩).trans (le_max_right _ _)⟩

private theorem decay_bound (f : PrincipalSeries positiveParameter) (x : ℂ) :
    ‖openCoordinate f x‖ ≤ chartSeminorm positiveParameter 0 f *
      Real.rpow 2 (4 / 3 : ℝ) * Real.rpow (1 + ‖x‖ ^ (2 : ℕ)) (-(4 / 3 : ℝ)) := by
  let M := chartSeminorm positiveParameter 0 f
  have hM : 0 ≤ M := by positivity
  have hbase : 0 < 1 + ‖x‖ ^ (2 : ℕ) := by positivity
  have hpow : 0 < Real.rpow (1 + ‖x‖ ^ (2 : ℕ)) (4 / 3 : ℝ) := Real.rpow_pos_of_pos hbase _
  have hr : Real.rpow (1 + ‖x‖ ^ (2 : ℕ)) (-(4 / 3 : ℝ)) = (Real.rpow (1 + ‖x‖ ^ (2 : ℕ)) (4 / 3 : ℝ))⁻¹ := by
    exact Real.rpow_neg hbase.le (4 / 3 : ℝ)
  rw [hr]
  apply (le_mul_inv_iff₀ hpow).2
  by_cases hx : ‖x‖ ≤ 1
  · have hval := (chart_zero_bound positiveParameter f x hx).1
    have hb : 1 + ‖x‖ ^ (2 : ℕ) ≤ 2 := by nlinarith [norm_nonneg x]
    have hp := Real.rpow_le_rpow hbase.le hb (show (0 : ℝ) ≤ 4 / 3 by norm_num)
    exact (mul_le_mul_of_nonneg_right hval hpow.le).trans
      (mul_le_mul_of_nonneg_left hp hM)
  · have hxpos : 0 < ‖x‖ := by linarith [norm_nonneg x]
    have hxn : x ≠ 0 := norm_pos_iff.mp hxpos
    have hu : ‖x⁻¹‖ ≤ 1 := by rw [norm_inv]; exact (inv_le_one₀ hxpos).2 (le_of_not_ge hx)
    have hval := (chart_zero_bound positiveParameter f (x⁻¹) hu).2
    have htrans := coordinate_transition positiveParameter f (x⁻¹) (inv_ne_zero hxn)
    rw [inv_inv] at htrans
    have hnorm := congrArg norm htrans
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hnorm
    have hw : transitionWeight positiveParameter (x⁻¹) = Real.rpow ‖x‖ (8 / 3 : ℝ) := by
      change Real.rpow ‖x⁻¹‖ (-2 * (1 + 2 * positiveParameter)) = _
      rw [norm_inv]
      have he : -2 * (1 + 2 * positiveParameter) = -(8 / 3 : ℝ) := by norm_num [positiveParameter]
      rw [he]
      have hi : Real.rpow ‖x‖⁻¹ (-(8 / 3 : ℝ)) = (Real.rpow ‖x‖ (-(8 / 3 : ℝ)))⁻¹ := Real.inv_rpow (norm_nonneg x) _
      rw [hi, show Real.rpow ‖x‖ (-(8 / 3 : ℝ)) = (Real.rpow ‖x‖ (8 / 3 : ℝ))⁻¹ from Real.rpow_neg (norm_nonneg x) _]
      simp
    rw [hw, abs_of_pos (show 0 < Real.rpow ‖x‖ (8 / 3 : ℝ) from Real.rpow_pos_of_pos hxpos _)] at hnorm
    have hb : 1 + ‖x‖ ^ (2 : ℕ) ≤ 2 * ‖x‖ ^ (2 : ℕ) := by nlinarith [le_of_not_ge hx]
    have hp := Real.rpow_le_rpow hbase.le hb (show (0 : ℝ) ≤ 4 / 3 by norm_num)
    have heq : Real.rpow (2 * ‖x‖ ^ (2 : ℕ)) (4 / 3 : ℝ) =
        Real.rpow 2 (4 / 3 : ℝ) * Real.rpow ‖x‖ (8 / 3 : ℝ) := by
      change (2 * ‖x‖ ^ (2 : ℕ)) ^ (4 / 3 : ℝ) = _
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg _),
        ← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg x)]
      norm_num
    change Real.rpow (1 + ‖x‖ ^ (2 : ℕ)) (4 / 3 : ℝ) ≤ Real.rpow (2 * ‖x‖ ^ (2 : ℕ)) (4 / 3 : ℝ) at hp
    rw [heq] at hp
    have hval' : ‖openCoordinate f x‖ * Real.rpow ‖x‖ (8 / 3 : ℝ) ≤ M := by
      rw [mul_comm, ← hnorm]; exact hval
    calc
      _ ≤ ‖openCoordinate f x‖ * (Real.rpow 2 (4 / 3 : ℝ) * Real.rpow ‖x‖ (8 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = (‖openCoordinate f x‖ * Real.rpow ‖x‖ (8 / 3 : ℝ)) * Real.rpow 2 (4 / 3 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hval' (Real.rpow_nonneg (by norm_num) _)
private theorem diagonal_one : diagonal (1 : ℂˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal]

private theorem kernel_integrable (β : ℂˣ) :
    Integrable (fun x : ℂ => Real.rpow (1 + ‖x‖ ^ (2 : ℕ)) (-(4 / 3 : ℝ))) (characterHaar β) := by
  have h := ((KPCplxIntertwinerEigenvalues.intertwinerIntegral_exists β
    (sphericalSection positiveParameter)).1 1).norm
  simp only [mul_one] at h
  convert h using 1
  funext x
  have he := sphericalSection_positive_open_diagonal x (1 : ℂˣ)
  simp only [diagonal_one, mul_one, Units.val_one, norm_one, show Real.rpow 1 (4 / 3 : ℝ) = 1 from Real.one_rpow _, one_pow, Complex.ofReal_one, one_mul] at he
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ Real.rpow (1 + ‖x‖ ^ (2 : ℕ)) (-(4 / 3 : ℝ)) from Real.rpow_nonneg (by positivity) _)]

private theorem jacquet_bound (β : ℂˣ) (f : PrincipalSeries positiveParameter) :
    ‖jacquetLinearMap β f‖ ≤ (Real.rpow 2 (4 / 3 : ℝ) *
      ∫ x : ℂ, Real.rpow (1 + ‖x‖ ^ (2 : ℕ)) (-(4 / 3 : ℝ)) ∂characterHaar β) *
      chartSeminorm positiveParameter 0 f := by
  have hb : ∀ x : ℂ, ‖f (weyl * upperUnipotent x) * (character (β : ℂ) (-x) : ℂ)‖ ≤
      chartSeminorm positiveParameter 0 f * Real.rpow 2 (4 / 3 : ℝ) *
      Real.rpow (1 + ‖x‖ ^ (2 : ℕ)) (-(4 / 3 : ℝ)) := by
    intro x
    rw [norm_mul, Circle.norm_coe, mul_one]
    exact decay_bound f x
  have h := norm_integral_le_of_norm_le ((kernel_integrable β).const_mul
    (chartSeminorm positiveParameter 0 f * Real.rpow 2 (4 / 3 : ℝ)))
    (Filter.Eventually.of_forall hb)
  change ‖jacquetLinearMap β f‖ ≤ _ at h
  rw [integral_const_mul] at h
  convert h using 1 <;> ring

theorem jacquetLinearMap_continuous (β : ℂˣ) :
    Continuous (jacquetLinearMap β) := by
  let C : ℝ := Real.rpow 2 (4 / 3 : ℝ) *
    ∫ x : ℂ, Real.rpow (1 + ‖x‖ ^ (2 : ℕ)) (-(4 / 3 : ℝ)) ∂characterHaar β
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (integral_nonneg fun x => Real.rpow_nonneg (by positivity) _)
  refine WithSeminorms.continuous_normedSpace_rng ℂ
    (show WithSeminorms (chartSeminorm positiveParameter) from ⟨rfl⟩)
    (jacquetLinearMap β) ⟨{0}, ⟨C, hC⟩, ?_⟩
  intro f
  simp only [Finset.sup_singleton]
  change ‖jacquetLinearMap β f‖ ≤ C * chartSeminorm positiveParameter 0 f
  exact jacquet_bound β f

noncomputable def jacquetFunctional (β : ℂˣ) :
    PrincipalSeries positiveParameter →L[ℂ] ℂ :=
  ⟨jacquetLinearMap β, jacquetLinearMap_continuous β⟩

@[simp] theorem jacquetFunctional_apply (β : ℂˣ) (f : PrincipalSeries positiveParameter) :
    jacquetFunctional β f =
      ∫ x : ℂ, f (weyl * upperUnipotent x) * (character (β : ℂ) (-x) : ℂ)
        ∂characterHaar β := rfl

theorem jacquetFunctional_covariance (β : ℂˣ) (t : ℂ)
    (f : PrincipalSeries positiveParameter) :
    jacquetFunctional β
        (pi positiveParameter (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f) =
      (character (β : ℂ) t : ℂ) * jacquetFunctional β f := by
  haveI := characterHaar_isAddHaarMeasure β
  rw [jacquetFunctional_apply, jacquetFunctional_apply]
  have hpt : ∀ x : ℂ, (pi positiveParameter (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f)
        (weyl * upperUnipotent x) = f (weyl * upperUnipotent (x + t)) := by
    intro x
    show f ((weyl * upperUnipotent x) * upperUnipotent t) = f (weyl * upperUnipotent (x + t))
    rw [weyl_upperUnipotent_mul]
  have hA : (∫ x : ℂ, (pi positiveParameter (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f)
        (weyl * upperUnipotent x) * (character (β : ℂ) (-x) : ℂ) ∂characterHaar β)
      = ∫ x : ℂ, f (weyl * upperUnipotent (x + t)) *
          (character (β : ℂ) (-x) : ℂ) ∂characterHaar β := by
    apply integral_congr_ae; filter_upwards with x; rw [hpt]
  rw [hA]
  have hB : (∫ x : ℂ, f (weyl * upperUnipotent (x + t)) *
        (character (β : ℂ) (-x) : ℂ) ∂characterHaar β)
      = ∫ x : ℂ, (character (β : ℂ) t : ℂ) *
          (f (weyl * upperUnipotent (x + t)) *
            (character (β : ℂ) (-(x + t)) : ℂ)) ∂characterHaar β := by
    apply integral_congr_ae
    filter_upwards with x
    have hc : (character (β : ℂ) (-x) : ℂ) =
        (character (β : ℂ) t : ℂ) * (character (β : ℂ) (-(x + t)) : ℂ) := by
      rw [show (-x : ℂ) = t + (-(x + t)) by ring,
        AddChar.map_add_eq_mul (character (β : ℂ)) t (-(x + t)), Circle.coe_mul]
    rw [hc]; ring
  rw [hB, integral_const_mul]
  congr 1
  have h1 : (fun x : ℂ => f (weyl * upperUnipotent (x + t)) *
        (character (β : ℂ) (-(x + t)) : ℂ))
      = fun x : ℂ => (fun u : ℂ => f (weyl * upperUnipotent u) *
        (character (β : ℂ) (-u) : ℂ)) (t + x) := by
    funext x; rw [add_comm t x]
  rw [h1]
  exact integral_add_left_eq_self (fun u : ℂ => f (weyl * upperUnipotent u) *
    (character (β : ℂ) (-u) : ℂ)) t

noncomputable def testBump : ContDiffBump (0 : ℂ) := ⟨1/2, 1, by norm_num, by norm_num⟩
private theorem character_smooth (β : ℂˣ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℂ => (character (β : ℂ) x : ℂ)) := by
  change ContDiff ℝ _ (fun x : ℂ => (Circle.exp (((β : ℂ) * x).re) : ℂ))
  simp only [Circle.coe_exp]
  apply ContDiff.cexp
  apply ContDiff.mul _ contDiff_const
  apply Complex.ofRealCLM.contDiff.comp
  exact Complex.reCLM.contDiff.comp (contDiff_const.mul contDiff_id)
noncomputable def testFunction (β : ℂˣ) (x : ℂ) : ℂ :=
  (testBump x : ℂ) * (character (β : ℂ) x : ℂ)
private theorem testFunction_smooth (β : ℂˣ) :
    ContDiff ℝ (⊤ : ℕ∞) (testFunction β) := by
  exact (Complex.ofRealCLM.contDiff.comp testBump.contDiff).mul (character_smooth β)
private theorem testFunction_vanish (β : ℂˣ) (x : ℂ) (hx : 1 ≤ ‖x‖) : testFunction β x = 0 := by
  have hzero : testBump x = 0 := by
    apply testBump.zero_of_le_dist
    simpa [testBump] using hx
  simp [testFunction, hzero]
private theorem testFunction_extends (β : ℂˣ) : ExtendsSmoothly positiveParameter (testFunction β) := by
  refine ⟨testFunction_smooth β, fun u => (transitionWeight positiveParameter u : ℂ) * testFunction β u⁻¹, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro u
    by_cases hu : u = 0
    · subst u
      have hz : (fun u : ℂ => (transitionWeight positiveParameter u : ℂ) * testFunction β u⁻¹) =ᶠ[𝓝 0] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with u hu
        by_cases h0 : u = 0
        · subst u
          have hz : transitionWeight positiveParameter 0 = 0 := by
            simp only [transitionWeight, norm_zero]
            change Real.rpow 0 (-2 * (1 + 2 * positiveParameter)) = 0
            exact Real.zero_rpow (by norm_num [positiveParameter])
          rw [hz, Complex.ofReal_zero, zero_mul]
        · have hn : ‖u‖ < 1 := by simpa using hu
          have hnpos : 0 < ‖u‖ := norm_pos_iff.mpr h0
          rw [testFunction_vanish β u⁻¹ (by rw [norm_inv]; exact (one_le_inv₀ hnpos).2 hn.le), mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hz
    · have hw : ContDiffAt ℝ (⊤ : ℕ∞) (transitionWeight positiveParameter) u := by
        exact (contDiffAt_norm ℂ hu).rpow_const_of_ne (norm_ne_zero_iff.mpr hu)
      exact (Complex.ofRealCLM.contDiff.contDiffAt.comp u hw).mul
        ((testFunction_smooth β).contDiffAt.comp u (contDiffAt_inv ℝ hu))
  · intro u hu
    rfl

theorem jacquetFunctional_ne_zero (β : ℂˣ) : jacquetFunctional β ≠ 0 := by
  letI : (characterHaar β).IsAddHaarMeasure := characterHaar_isAddHaarMeasure β
  obtain ⟨f, hf⟩ := (openCoordinate_range positiveParameter (testFunction β)).2
    (testFunction_extends β)
  have he : jacquetFunctional β f = ((∫ x : ℂ, testBump x ∂characterHaar β : ℝ) : ℂ) := by
    rw [jacquetFunctional_apply]
    calc
      _ = ∫ x : ℂ, (testBump x : ℂ) ∂characterHaar β := ?_
      _ = _ := integral_ofReal

    apply integral_congr_ae
    filter_upwards with x
    change openCoordinate f x * (character (β : ℂ) (-x) : ℂ) = _
    rw [hf]
    dsimp [testFunction]
    rw [mul_assoc, AddChar.map_neg_eq_inv, Circle.coe_inv, mul_inv_cancel₀ (Circle.coe_ne_zero _), mul_one]
  have hp := testBump.integral_pos (μ := characterHaar β)
  intro hz
  have hzero : jacquetFunctional β f = 0 := by rw [hz]; rfl
  rw [he] at hzero
  exact hp.ne' (Complex.ofReal_eq_zero.mp hzero)

noncomputable def sourceImageEquiv (β : ℂˣ) :
    PrincipalSeries positiveParameter ≃L[ℂ] Theta β :=
  Classical.choose (standardIntertwiner_topological_image_isomorphism β)

private theorem sourceImageEquiv_apply (β : ℂˣ) (f : PrincipalSeries positiveParameter) :
    sourceImageEquiv β f = intertwinerToImage β f :=
  (Classical.choose_spec (standardIntertwiner_topological_image_isomorphism β)).1 f

noncomputable def thetaJacquetFunctional (β : ℂˣ) : Theta β →L[ℂ] ℂ :=
  (jacquetFunctional β).comp (sourceImageEquiv β).symm.toContinuousLinearMap

@[simp] theorem thetaJacquetFunctional_intertwiner (β : ℂˣ)
    (f : PrincipalSeries positiveParameter) :
    thetaJacquetFunctional β (intertwinerToImage β f) = jacquetFunctional β f := by
  change jacquetFunctional β ((sourceImageEquiv β).symm (intertwinerToImage β f)) = _
  rw [← sourceImageEquiv_apply β f, ContinuousLinearEquiv.symm_apply_apply]

theorem thetaJacquetFunctional_covariance (β : ℂˣ) (t : ℂ) (h : Theta β) :
    thetaJacquetFunctional β
        (imageAction β (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) h) =
      (character (β : ℂ) t : ℂ) * thetaJacquetFunctional β h := by
  obtain ⟨f, hf⟩ := (mem_imageSubmodule_iff β (h : PrincipalSeries negativeParameter)).1 h.property
  have hh : h = intertwinerToImage β f := by
    apply Subtype.ext
    rw [← hf, intertwinerToImage_coe]
  rw [hh, ← intertwinerToImage_equivariant β (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f,
    thetaJacquetFunctional_intertwiner, jacquetFunctional_covariance,
    thetaJacquetFunctional_intertwiner]

theorem thetaJacquetFunctional_ne_zero (β : ℂˣ) : thetaJacquetFunctional β ≠ 0 := by
  intro h
  apply jacquetFunctional_ne_zero β
  ext f
  rw [← thetaJacquetFunctional_intertwiner β f, h]
  simp

theorem jacquetFunctional_spherical_diagonal (β : ℂˣ) (y : ℂˣ) :
    jacquetFunctional β
        (pi positiveParameter (Matrix.ProjGenLinGroup.mk (diagonal y))
          (sphericalSection positiveParameter)) =
      ∫ x : ℂ,
        ((Real.rpow ‖(y : ℂ)‖ (4 / 3) *
          Real.rpow (‖(y : ℂ)‖ ^ 2 + ‖x‖ ^ 2) (-(4 / 3)) : ℝ) : ℂ) *
            (character (β : ℂ) (-x) : ℂ) ∂characterHaar β := by
  rw [jacquetFunctional_apply]
  apply integral_congr_ae
  filter_upwards with x
  rw [show (pi positiveParameter (Matrix.ProjGenLinGroup.mk (diagonal y))
        (sphericalSection positiveParameter)) (weyl * upperUnipotent x)
      = sphericalSection positiveParameter (weyl * upperUnipotent x * diagonal y) from rfl]
  rw [sphericalSection_positive_open_diagonal, ← Complex.ofReal_mul]

theorem jacquetFunctional_spherical_diagonal_positive (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (y : ℂˣ) :
    jacquetFunctional β
        (pi positiveParameter (Matrix.ProjGenLinGroup.mk (diagonal y))
          (sphericalSection positiveParameter)) =
      ∫ x : ℂ,
        ((Real.rpow ‖(y : ℂ)‖ (4 / 3) *
          Real.rpow (‖(y : ℂ)‖ ^ 2 + ‖x‖ ^ 2) (-(4 / 3)) : ℝ) : ℂ) *
            Complex.exp (-Complex.I * (c : ℂ) * (x.re : ℂ)) ∂characterHaar β := by
  rw [jacquetFunctional_spherical_diagonal β y]
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  rw [show (character (β : ℂ) (-x) : ℂ) =
        (Circle.exp (((β : ℂ) * (-x)).re) : ℂ) from rfl, Circle.coe_exp]
  rw [hβ]
  congr 1
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
  push_cast
  ring

end DedekindZetaZeroFree.KPCplxJacquetFunctional
