module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.CoreShellPartition
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.BoundaryFlux.AngularConormalDescent

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory Filter
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes renaming continuous_core_integrable → continuous_core_integrable
namespace DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.CutoffApproximation
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

 theorem admissible_mono {Y T : ℝ}
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y) (hYT : Y ≤ T) :
    KPMsFixedHaarDisintegration.AdmissibleCutoff A T := by
  refine ⟨lt_of_lt_of_le hY.1 hYT, hY.2.trans ?_⟩
  exact div_le_div_of_nonneg_right (Real.log_le_log hY.1 hYT) (by positivity)

 theorem modulus_gt_of_not_core
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (x : X F ζ hζ) (hx : x ∉ quotientCore A P Y) :
    Y < D.modulus (P.projection U x) := by
  have he : P.projection U x ∈ KPMsFixedHaarDisintegration.cuspEnds A Y := by
    simp only [quotientCore, Set.mem_ofPred_eq, not_forall, not_not] at hx
    obtain ⟨j,hj⟩ := hx
    exact Set.mem_iUnion.mpr ⟨j,hj⟩
  rw [← D.chart_range Y hY] at he
  obtain ⟨⟨c,r⟩,hr⟩ := he
  rw [← hr, D.chart_modulus Y hY c r]
  exact r.property

 theorem cutoff_measurable
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y ε : ℝ) : Measurable (coreCutoff A R P D Y ε) := by
  let : BorelSpace (X F ζ hζ) := ⟨rfl⟩
  exact Measurable.ite (FiniteSlabCoreShell.isClosed_quotientCore A P Y).measurableSet
    measurable_const (measurable_const.max (measurable_const.min
      ((measurable_const.sub (D.measurable_modulus.comp (P.continuous U).measurable)).div_const ε)))

 theorem cutoff_bound
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y ε : ℝ) (x : X F ζ hζ) : |coreCutoff A R P D Y ε x| ≤ 1 := by
  unfold coreCutoff
  split_ifs with hx
  · norm_num
  · rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le (by norm_num) (min_le_left _ _)

private theorem cutoff_support
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (ε : ℝ) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (x : X F ζ hζ) (hx : x ∉ quotientCore A P (Y+1)) :
    coreCutoff A R P D Y ε x = 0 := by
  have hxY : x ∉ quotientCore A P Y := fun h => hx
    (FiniteSlabCoreShell.quotientCore_mono A P hY.1 (by linarith) h)
  have hm := modulus_gt_of_not_core A R P D (Y+1) (admissible_mono A hY (by linarith)) x hx
  simp only [coreCutoff, ite_eq_right hxY]
  have hq : (Y+ε-D.modulus (P.projection U x))/ε ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  exact max_eq_left (le_trans (min_le_right _ _) hq)

private theorem cutoff_pointwise
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (x : X F ζ hζ) :
    Tendsto (fun ε => coreCutoff A R P D Y ε x) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 ((quotientCore A P Y).indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : x ∈ quotientCore A P Y
  · simp only [coreCutoff, ite_eq_left hx, Set.indicator_of_mem hx]
    exact tendsto_const_nhds
  · rw [Set.indicator_of_notMem hx]
    have hm := modulus_gt_of_not_core A R P D Y hY x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show 0 < D.modulus (P.projection U x)-Y by linarith)).filter_mono
        nhdsWithin_le_nhds] with ε hε hsmall
    simp only [coreCutoff, ite_eq_right hx]
    have hq : (Y+ε-D.modulus (P.projection U x))/ε ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
    exact (max_eq_left (le_trans (min_le_right _ _) hq)).symm

theorem cutoffIntegral_tendsto
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (f : X F ζ hζ → ℂ) (hf : Continuous f) :
    Filter.Tendsto (fun ε : ℝ => cutoffIntegral A R P D Y ε f)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x in quotientCore A P Y, f x ∂ R.quotientHaar)) := by
  let : BorelSpace (X F ζ hζ) := ⟨rfl⟩
  have had := admissible_mono A hY (show Y ≤ Y+1 by linarith)
  have hfi : IntegrableOn f (quotientCore A P (Y+1)) R.quotientHaar :=
    continuous_core_integrable A R P (Y+1) had f hf
  have hm := (FiniteSlabCoreShell.isClosed_quotientCore A P (Y+1)).measurableSet
  have hs := (FiniteSlabCoreShell.isClosed_quotientCore A P Y).measurableSet
  have hsub : quotientCore A P Y ⊆ quotientCore A P (Y+1) :=
    FiniteSlabCoreShell.quotientCore_mono A P hY.1 (by linarith)
  have he : (fun ε : ℝ => ∫ x, (coreCutoff A R P D Y ε x : ℂ) * f x
      ∂(R.quotientHaar.restrict (quotientCore A P (Y+1))))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun ε => cutoffIntegral A R P D Y ε f) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with ε hε hε₁
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp only [cutoff_support A R P D Y hY ε hε hε₁.le x hx,
        Complex.ofReal_zero, zero_mul]
  have hi : (∫ x, (quotientCore A P Y).indicator f x
      ∂(R.quotientHaar.restrict (quotientCore A P (Y+1)))) =
      ∫ x in quotientCore A P Y, f x ∂ R.quotientHaar := by
    rw [integral_indicator hs, Measure.restrict_restrict_of_subset hsub]
  apply Tendsto.congr' he
  rw [← hi]
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
  · exact Eventually.of_forall fun ε =>
      (Complex.continuous_ofReal.comp_aestronglyMeasurable
        (cutoff_measurable A R P D Y ε).aestronglyMeasurable).mul hfi.aestronglyMeasurable
  · exact Eventually.of_forall fun ε => Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using cutoff_bound A R P D Y ε x)
  · exact hfi.norm
  · exact Eventually.of_forall fun x => by
      have ht := (Complex.continuous_ofReal.tendsto _).comp
        (cutoff_pointwise A R P D Y hY x)
      have ht' := ht.mul_const (f x)
      have hi' : Complex.ofReal ((quotientCore A P Y).indicator (fun _ => (1 : ℝ)) x) * f x =
          (quotientCore A P Y).indicator f x := by
        by_cases hx : x ∈ quotientCore A P Y <;> simp [hx]
      rw [hi'] at ht'
      exact ht'

end DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.CutoffApproximation

end
