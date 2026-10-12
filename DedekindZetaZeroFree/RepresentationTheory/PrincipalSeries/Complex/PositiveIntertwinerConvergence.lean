module
public import Mathlib.MeasureTheory.Integral.Asymptotics

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicKTypes

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped BigOperators
open Filter Asymptotics

private lemma transition_norm (f : PrincipalSeries positiveParameter) (x : ℂ)
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

private lemma tail_bigO (f : PrincipalSeries positiveParameter) :
    openCoordinate f =O[cocompact ℂ] (fun x : ℂ => (1 + ‖x‖) ^ (-(8 / 3 : ℝ))) := by
  have hcont : Continuous (infinityCoordinate f) := f.property.2.2.continuous
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hcont.continuousOn
  refine isBigO_iff.mpr ⟨max C 0 * (2 : ℝ) ^ (8 / 3 : ℝ), ?_⟩
  have hev : ∀ᶠ x : ℂ in cocompact ℂ, 1 ≤ ‖x‖ := by
    filter_upwards [(isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact] with x hx
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hx.le
  filter_upwards [hev] with x hx
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx; norm_num at hx
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hxi : x⁻¹ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right, norm_inv]
    exact inv_le_one_of_one_le₀ hx
  have hi := (hC x⁻¹ hxi).trans (le_max_left C 0)
  have hp : ‖x‖ ^ (-(8 / 3 : ℝ)) ≤
      (2 : ℝ) ^ (8 / 3 : ℝ) * (1 + ‖x‖) ^ (-(8 / 3 : ℝ)) := by
    have ht : (1 + ‖x‖) / 2 ≤ ‖x‖ := by linarith
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1 + ‖x‖) / 2) ht
      (by norm_num : -(8 / 3 : ℝ) ≤ 0)
    rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul] at h
    simpa only [mul_comm] using h
  rw [transition_norm f x hx]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc
    _ ≤ ‖x‖ ^ (-(8 / 3 : ℝ)) * max C 0 := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg (norm_nonneg _) _)
    _ ≤ ((2 : ℝ) ^ (8 / 3 : ℝ) * (1 + ‖x‖) ^ (-(8 / 3 : ℝ))) * max C 0 :=
      mul_le_mul_of_nonneg_right hp (le_max_right C 0)
    _ = _ := by ring

theorem positive_intertwiner_integrable (β : ℂˣ)
    (f : PrincipalSeries positiveParameter) (g : ComplexGL2) :
    Integrable (fun x : ℂ => f (weyl * upperUnipotent x * g)) (characterHaar β) := by
  letI := characterHaar_isAddHaarMeasure β
  let F := rightTranslate positiveParameter g f
  change Integrable (openCoordinate F) (characterHaar β)
  have hcont : Continuous (openCoordinate F) := F.property.2.1.continuous
  apply hcont.locallyIntegrable.integrable_of_isBigO_cocompact (tail_bigO F)
  apply (integrable_iff_integrableAtFilter_cocompact.mp ?_).1
  exact integrable_one_add_norm (by norm_num [Complex.finrank_real_complex])
end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
