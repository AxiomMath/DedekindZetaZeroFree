module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ComplexChartsAndSphericalSections

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory Set
open scoped NNReal

lemma openCoordinate_norm_le_chartSeminorm_zero (s : ℝ) (f : PrincipalSeries s)
    (x : ℂ) (hx : x ∈ Metric.closedBall (0 : ℂ) 1) :
    ‖openCoordinate f x‖ ≤ chartSeminorm s 0 f := by
  have hc : Continuous (fun x : ℂ => ‖iteratedFDeriv ℝ 0 (openCoordinate f) x‖) :=
    (f.property.2.1.continuous_iteratedFDeriv (by simp)).norm
  have hb := (isCompact_closedBall (0 : ℂ) 1).image hc
  change ‖openCoordinate f x‖ ≤ chartSeminormValue s 0 f
  unfold chartSeminormValue
  apply le_trans ?_ (le_max_left _ _)
  simpa using le_csSup hb.bddAbove (mem_image_of_mem _ hx)

lemma infinityCoordinate_norm_le_chartSeminorm_zero (s : ℝ) (f : PrincipalSeries s)
    (x : ℂ) (hx : x ∈ Metric.closedBall (0 : ℂ) 1) :
    ‖infinityCoordinate f x‖ ≤ chartSeminorm s 0 f := by
  have hc : Continuous (fun x : ℂ => ‖iteratedFDeriv ℝ 0 (infinityCoordinate f) x‖) :=
    (f.property.2.2.continuous_iteratedFDeriv (by simp)).norm
  have hb := (isCompact_closedBall (0 : ℂ) 1).image hc
  change ‖infinityCoordinate f x‖ ≤ chartSeminormValue s 0 f
  unfold chartSeminormValue
  apply le_trans ?_ (le_max_right _ _)
  simpa using le_csSup hb.bddAbove (mem_image_of_mem _ hx)

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory Set
open scoped NNReal

private lemma positive_transition_norm (f : PrincipalSeries positiveParameter) (x : ℂ)
    (hx : 1 ≤ ‖x‖) :
    ‖openCoordinate f x‖ = ‖x‖ ^ (-(8 / 3 : ℝ)) * ‖infinityCoordinate f x⁻¹‖ := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx; norm_num at hx
  have h := coordinate_transition positiveParameter f x⁻¹ (inv_ne_zero hx0)
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hw : transitionWeight positiveParameter x⁻¹ = ‖x‖ ^ (8 / 3 : ℝ) := by
    simp only [transitionWeight, positiveParameter, norm_inv]
    norm_num
    rw [Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)]
    norm_num
  rw [inv_inv, hw] at h
  have hn := congrArg norm h
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hxp _)] at hn
  have hr : ‖x‖ ^ (-(8 / 3 : ℝ)) * ‖x‖ ^ (8 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hxp]; norm_num
  rw [hn, ← mul_assoc, hr, one_mul]

lemma positive_openCoordinate_uniform_envelope (f : PrincipalSeries positiveParameter) (x : ℂ) :
    ‖openCoordinate f x‖ ≤ (2 : ℝ) ^ (8 / 3 : ℝ) * chartSeminorm positiveParameter 0 f *
      (1 + ‖x‖) ^ (-(8 / 3 : ℝ)) := by
  have hs : 0 ≤ chartSeminorm positiveParameter 0 f := apply_nonneg _ _
  by_cases hx : 1 ≤ ‖x‖
  · have hxi : x⁻¹ ∈ Metric.closedBall (0 : ℂ) 1 := by
      simp only [Metric.mem_closedBall, dist_zero_right, norm_inv]
      exact inv_le_one_of_one_le₀ hx
    have hi := infinityCoordinate_norm_le_chartSeminorm_zero positiveParameter f x⁻¹ hxi
    have hp : ‖x‖ ^ (-(8 / 3 : ℝ)) ≤
        (2 : ℝ) ^ (8 / 3 : ℝ) * (1 + ‖x‖) ^ (-(8 / 3 : ℝ)) := by
      have ht : (1 + ‖x‖) / 2 ≤ ‖x‖ := by linarith
      have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1 + ‖x‖) / 2) ht
        (by norm_num : -(8 / 3 : ℝ) ≤ 0)
      rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul] at h
      simpa only [mul_comm] using h
    rw [positive_transition_norm f x hx]
    calc
      _ ≤ ‖x‖ ^ (-(8 / 3 : ℝ)) * chartSeminorm positiveParameter 0 f :=
        mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ ((2 : ℝ) ^ (8 / 3 : ℝ) * (1 + ‖x‖) ^ (-(8 / 3 : ℝ))) *
          chartSeminorm positiveParameter 0 f := mul_le_mul_of_nonneg_right hp hs
      _ = _ := by ring
  · have hball : x ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using (le_of_not_ge hx)
    have ho := openCoordinate_norm_le_chartSeminorm_zero positiveParameter f x hball
    have hw : 1 ≤ (2 : ℝ) ^ (8 / 3 : ℝ) * (1 + ‖x‖) ^ (-(8 / 3 : ℝ)) := by
      have h := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < 1 + ‖x‖)
        (by linarith [le_of_not_ge hx] : 1 + ‖x‖ ≤ (2 : ℝ)) (by norm_num : -(8 / 3 : ℝ) ≤ 0)
      have he : (2 : ℝ) ^ (8 / 3 : ℝ) * (2 : ℝ) ^ (-(8 / 3 : ℝ)) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; norm_num
      calc
        1 = (2 : ℝ) ^ (8 / 3 : ℝ) * (2 : ℝ) ^ (-(8 / 3 : ℝ)) := he.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num) _)
    calc
      _ ≤ chartSeminorm positiveParameter 0 f := ho
      _ ≤ ((2 : ℝ) ^ (8 / 3 : ℝ) * (1 + ‖x‖) ^ (-(8 / 3 : ℝ))) *
          chartSeminorm positiveParameter 0 f := by simpa using mul_le_mul_of_nonneg_right hw hs
      _ = _ := by ring

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory Set
open scoped NNReal

lemma positive_openCoordinate_integral_bound (β : ℂˣ) :
    ∃ C : ℝ≥0, ∀ f : PrincipalSeries positiveParameter,
      ‖∫ x : ℂ, openCoordinate f x ∂characterHaar β‖ ≤ C * chartSeminorm positiveParameter 0 f := by
  letI := characterHaar_isAddHaarMeasure β
  let w : ℂ → ℝ := fun x => (1 + ‖x‖) ^ (-(8 / 3 : ℝ))
  have hw : Integrable w (characterHaar β) := by
    apply integrable_one_add_norm
    simp only [Complex.finrank_real_complex]
    norm_num
  let C : ℝ := (2 : ℝ) ^ (8 / 3 : ℝ) * ∫ x : ℂ, w x ∂characterHaar β
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (integral_nonneg (fun x => Real.rpow_nonneg (by positivity) _))
  refine ⟨⟨C, hC⟩, ?_⟩
  intro f
  have hb := norm_integral_le_of_norm_le
    (hw.const_mul ((2 : ℝ) ^ (8 / 3 : ℝ) * chartSeminorm positiveParameter 0 f))
    (Filter.Eventually.of_forall (positive_openCoordinate_uniform_envelope f))
  rw [integral_const_mul] at hb
  change _ ≤ C * chartSeminorm positiveParameter 0 f
  dsimp [C]
  convert hb using 1 <;> ring

lemma positive_openCoordinate_integrable (β : ℂˣ) (f : PrincipalSeries positiveParameter) :
    Integrable (openCoordinate f) (characterHaar β) := by
  letI := characterHaar_isAddHaarMeasure β
  have hw : Integrable (fun x : ℂ => (1 + ‖x‖) ^ (-(8 / 3 : ℝ))) (characterHaar β) := by
    apply integrable_one_add_norm
    simp only [Complex.finrank_real_complex]
    norm_num
  exact (hw.const_mul ((2 : ℝ) ^ (8 / 3 : ℝ) * chartSeminorm positiveParameter 0 f)).mono'
    f.property.2.1.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (positive_openCoordinate_uniform_envelope f))

noncomputable def positive_openCoordinate_integralLinearMap (β : ℂˣ) :
    PrincipalSeries positiveParameter →ₗ[ℂ] ℂ where
  toFun f := ∫ x : ℂ, openCoordinate f x ∂characterHaar β
  map_add' f g := by
    change (∫ x : ℂ, openCoordinate f x + openCoordinate g x ∂characterHaar β) = _
    exact integral_add (positive_openCoordinate_integrable β f) (positive_openCoordinate_integrable β g)
  map_smul' c f := by
    change (∫ x : ℂ, c • openCoordinate f x ∂characterHaar β) = _
    exact integral_smul c _

lemma positive_openCoordinate_integralLinearMap_continuous (β : ℂˣ) :
    Continuous (positive_openCoordinate_integralLinearMap β) := by
  have htop : WithSeminorms (chartSeminorm positiveParameter) := ⟨rfl⟩
  obtain ⟨C, hC⟩ := positive_openCoordinate_integral_bound β
  apply htop.continuous_of_isBounded (norm_withSeminorms ℂ ℂ)
  intro i
  refine ⟨{0}, C, ?_⟩
  rw [Finset.sup_singleton, Seminorm.le_def]
  intro f
  simpa [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, positive_openCoordinate_integralLinearMap] using hC f

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory Set
open scoped NNReal

lemma positive_rightTranslate_continuous (g : ComplexGL2) :
    Continuous (rightTranslate positiveParameter g) := by
  have hh := pi_continuous positiveParameter
  have h := hh.comp (continuous_const.prodMk continuous_id :
    Continuous (fun f : PrincipalSeries positiveParameter =>
      (Matrix.ProjGenLinGroup.mk g, f)))
  simpa only [Function.comp_def, pi_mk] using h

lemma positive_intertwiner_point_evaluation_continuous (β : ℂˣ)
    (T : PrincipalSeries positiveParameter →ₗ[ℂ] PrincipalSeries negativeParameter)
    (hT : ∀ (f : PrincipalSeries positiveParameter) (g : ComplexGL2),
      T f g = ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β)
    (g : ComplexGL2) : Continuous (fun f => T f g) := by
  have h := (positive_openCoordinate_integralLinearMap_continuous β).comp
    (positive_rightTranslate_continuous g)
  convert h using 1
  funext f
  rw [hT]
  rfl

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

open MeasureTheory Filter
open scoped Topology
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts

lemma principalSeries_barrelled (s : ℝ) : BarrelledSpace ℝ (PrincipalSeries s) := by
  letI := principalSeries_t2 s
  letI := principalSeries_metrizable s
  letI := principalSeries_complete s
  have htop : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  letI : ContinuousSMul ℂ (PrincipalSeries s) := htop.continuousSMul
  letI : ContinuousSMul ℝ (PrincipalSeries s) := ⟨by
    have hh := (Complex.continuous_ofReal.comp continuous_fst).smul (continuous_snd :
      Continuous (fun p : ℝ × PrincipalSeries s => p.2))
    change Continuous (fun p : ℝ × PrincipalSeries s => (algebraMap ℝ ℂ) p.1 • p.2) at hh
    simpa only [IsScalarTower.algebraMap_smul] using hh⟩
  letI : IsUniformAddGroup (PrincipalSeries s) := isUniformAddGroup_of_addCommGroup
  letI := IsUniformAddGroup.uniformity_countably_generated (α := PrincipalSeries s)
  infer_instance

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul ℝ E] [BarrelledSpace ℝ E]
    (A : E →ₗ[ℝ] (ℂ → ℂ)) (hA : ∀ f, ContDiff ℝ (⊤ : ℕ∞) (A f))

noncomputable def derivativeEvaluationLinearMap (n : ℕ) (x : ℂ) : E →ₗ[ℝ] (ℂ [×n]→L[ℝ] ℂ) where
  toFun f := iteratedFDeriv ℝ n (A f) x
  map_add' f g := by
    rw [A.map_add]
    exact congrFun (iteratedFDeriv_add ((hA f).of_le (by simp)) ((hA g).of_le (by simp))) x
  map_smul' c f := by
    rw [A.map_smul]
    exact iteratedFDeriv_const_smul_apply ((hA f).contDiffAt.of_le (by simp))

lemma derivativeEvaluation_continuous (hA : ∀ f, ContDiff ℝ (⊤ : ℕ∞) (A f))
    (hcont : ∀ x : ℂ, Continuous (fun f => A f x)) :
    ∀ n : ℕ, ∀ x : ℂ, Continuous (fun f => iteratedFDeriv ℝ n (A f) x) := by
  intro n
  induction n with
  | zero =>
    intro x
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ ℂ ℂ).symm.continuous.comp (hcont x)
  | succ n ih =>
    intro x
    have hc : Continuous (fun f => fderiv ℝ (iteratedFDeriv ℝ n (A f)) x) := by
      apply continuous_clm_apply.mpr
      intro v
      let D (t : ℝ) : E →L[ℝ] (ℂ [×n]→L[ℝ] ℂ) :=
        t⁻¹ • ((⟨derivativeEvaluationLinearMap A hA n (x + t • v), ih _⟩ : E →L[ℝ] _) -
          (⟨derivativeEvaluationLinearMap A hA n x, ih _⟩ : E →L[ℝ] _))
      have ht : Tendsto (fun t f => D t f) (𝓝[≠] (0 : ℝ))
          (𝓝 (fun f => fderiv ℝ (iteratedFDeriv ℝ n (A f)) x v)) := by
        rw [tendsto_pi_nhds]
        intro f
        have hd : Differentiable ℝ (iteratedFDeriv ℝ n (A f)) :=
          ContDiff.differentiable_iteratedFDeriv (m := n)
            (by exact_mod_cast (ENat.coe_lt_top n)) (hA f)
        have hinner := ((hasFDerivAt_const (𝕜 := ℝ) x (0 : ℝ)).add
          ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const v))
        have hh := (hd _).hasFDerivAt.comp (0 : ℝ) hinner
        have hder : HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ n (A f) (x + t • v))
            (fderiv ℝ (iteratedFDeriv ℝ n (A f)) x v) 0 := by
          convert hh.hasDerivAt using 1 <;> simp [Function.comp_def]
        change Tendsto (fun t : ℝ => t⁻¹ •
          (iteratedFDeriv ℝ n (A f) (x + t • v) - iteratedFDeriv ℝ n (A f) x)) _ _
        simpa only [zero_add, zero_smul, add_zero] using hder.tendsto_slope_zero
      exact (continuousLinearMapOfTendsto D ht).continuous
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => ℂ) ℂ).symm.continuous.comp hc

end
end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts Set

lemma principalSeries_barrelled_complex (s : ℝ) : BarrelledSpace ℂ (PrincipalSeries s) := by
  letI := principalSeries_t2 s
  letI := principalSeries_metrizable s
  letI := principalSeries_complete s
  have htop : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  letI : ContinuousSMul ℂ (PrincipalSeries s) := htop.continuousSMul
  letI : IsUniformAddGroup (PrincipalSeries s) := isUniformAddGroup_of_addCommGroup
  letI := IsUniformAddGroup.uniformity_countably_generated (α := PrincipalSeries s)
  infer_instance

lemma closedDiscSup_lowerSemicontinuous {E : Type*} [TopologicalSpace E]
    (F : E → ℂ → ℝ) (hF : ∀ x : ℂ, Continuous (fun f => F f x))
    (hcont : ∀ f, Continuous (F f)) :
    LowerSemicontinuous (fun f => sSup (F f '' Metric.closedBall (0 : ℂ) 1)) := by
  let B := Metric.closedBall (0 : ℂ) 1
  letI : Nonempty B := ⟨⟨0, Metric.mem_closedBall_self (by norm_num)⟩⟩
  have he : (fun f => sSup (F f '' B)) = fun f => ⨆ x : B, F f x := by
    funext f
    rw [iSup]
    congr 1
    ext r
    simp [Set.mem_range]
  rw [he]
  apply lowerSemicontinuous_ciSup
  · intro f
    have hb := ((isCompact_closedBall (0 : ℂ) 1).image (hcont f)).bddAbove
    exact hb.mono (by rintro r ⟨x, rfl⟩; exact ⟨x, x.property, rfl⟩)
  · intro x
    exact (hF x).lowerSemicontinuous

lemma linearMap_continuous_of_point_evaluations (s t : ℝ)
    (T : PrincipalSeries s →ₗ[ℂ] PrincipalSeries t)
    (hT : ∀ g : ComplexGL2, Continuous (fun f => T f g)) : Continuous T := by
  letI : BarrelledSpace ℝ (PrincipalSeries s) := principalSeries_barrelled s
  letI : BarrelledSpace ℂ (PrincipalSeries s) := principalSeries_barrelled_complex s
  have htop : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  letI : ContinuousSMul ℂ (PrincipalSeries s) := htop.continuousSMul
  letI : ContinuousSMul ℝ (PrincipalSeries s) := ⟨by
    have hh := (Complex.continuous_ofReal.comp continuous_fst).smul (continuous_snd :
      Continuous (fun p : ℝ × PrincipalSeries s => p.2))
    change Continuous (fun p : ℝ × PrincipalSeries s => (algebraMap ℝ ℂ) p.1 • p.2) at hh
    simpa only [IsScalarTower.algebraMap_smul] using hh⟩
  letI : IsUniformAddGroup (PrincipalSeries s) := isUniformAddGroup_of_addCommGroup
  let O : PrincipalSeries s →ₗ[ℝ] (ℂ → ℂ) :=
    { toFun := fun f => openCoordinate (T f)
      map_add' := by intros; ext; simp [openCoordinate]
      map_smul' := by intros; ext; simp [openCoordinate] }
  let I : PrincipalSeries s →ₗ[ℝ] (ℂ → ℂ) :=
    { toFun := fun f => infinityCoordinate (T f)
      map_add' := by intros; ext; simp [infinityCoordinate]
      map_smul' := by intros; ext; simp [infinityCoordinate] }
  have ho := derivativeEvaluation_continuous O (fun f => (T f).property.2.1)
    (fun x => hT (weyl * upperUnipotent x))
  have hi := derivativeEvaluation_continuous I (fun f => (T f).property.2.2)
    (fun x => hT (lowerUnipotent x))
  have ht : WithSeminorms (chartSeminorm t) := ⟨rfl⟩
  apply ht.continuous_of_continuous_comp T
  intro n
  apply Seminorm.continuous_of_lowerSemicontinuous
  change LowerSemicontinuous (fun f => chartSeminormValue t n (T f))
  unfold chartSeminormValue
  apply LowerSemicontinuous.sup
  · apply closedDiscSup_lowerSemicontinuous
    · intro x; exact (ho n x).norm
    · intro f; exact ((T f).property.2.1.continuous_iteratedFDeriv (by simp)).norm
  · apply closedDiscSup_lowerSemicontinuous
    · intro x; exact (hi n x).norm
    · intro f; exact ((T f).property.2.2.continuous_iteratedFDeriv (by simp)).norm

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory Set
open scoped NNReal
lemma openCoordinate_derivative_le_chartSeminorm (s : ℝ) (n : ℕ) (f : PrincipalSeries s)
    (x : ℂ) (hx : x ∈ Metric.closedBall (0 : ℂ) 1) :
    ‖iteratedFDeriv ℝ n (openCoordinate f) x‖ ≤ chartSeminorm s n f := by
  have hc : Continuous (fun x : ℂ => ‖iteratedFDeriv ℝ n (openCoordinate f) x‖) :=
    (f.property.2.1.continuous_iteratedFDeriv (by simp)).norm
  have hb := (isCompact_closedBall (0 : ℂ) 1).image hc
  change _ ≤ chartSeminormValue s n f
  unfold chartSeminormValue
  exact (le_csSup hb.bddAbove (mem_image_of_mem _ hx)).trans (le_max_left _ _)

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped NNReal

theorem positive_intertwiner_open_chart_bounds (β : ℂˣ)
    (T : PrincipalSeries positiveParameter →ₗ[ℂ] PrincipalSeries negativeParameter)
    (hT : ∀ (f : PrincipalSeries positiveParameter) (g : ComplexGL2),
      T f g = ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β) :
    ∀ n : ℕ, ∃ (orders : Finset ℕ) (C : ℝ≥0),
      ∀ (f : PrincipalSeries positiveParameter) (x : ℂ),
        x ∈ Metric.closedBall (0 : ℂ) 1 →
          ‖iteratedFDeriv ℝ n (openCoordinate (T f)) x‖ ≤
            (C • orders.sup (chartSeminorm positiveParameter)) f := by
  have hc := linearMap_continuous_of_point_evaluations positiveParameter negativeParameter T
    (positive_intertwiner_point_evaluation_continuous β T hT)
  have htop : WithSeminorms (chartSeminorm positiveParameter) := ⟨rfl⟩
  have ht : WithSeminorms (chartSeminorm negativeParameter) := ⟨rfl⟩
  intro n
  obtain ⟨orders, C, _, hb⟩ := Seminorm.bound_of_continuous htop
    ((chartSeminorm negativeParameter n).comp T) ((ht.continuous_seminorm n).comp hc)
  refine ⟨orders, C, ?_⟩
  intro f x hx
  exact (openCoordinate_derivative_le_chartSeminorm negativeParameter n (T f) x hx).trans
    (Seminorm.le_def.mp hb f)

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
