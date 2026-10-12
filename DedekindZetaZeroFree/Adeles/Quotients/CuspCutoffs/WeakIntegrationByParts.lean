module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspCutoffs.GlobalRegularity

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory Filter
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.CutoffApproximation renaming cutoff_measurable → cutoff_measurable
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.CutoffApproximation renaming cutoff_bound → cutoff_bound
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.CutoffApproximation renaming modulus_gt_of_not_core → modulus_gt_of_not_core
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.CutoffApproximation renaming admissible_mono → admissible_mono
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes renaming continuous_core_integrable → continuous_core_integrable
open scoped NumberField Topology BigOperators
open MeasureTheory Filter
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming bottomRowJet → bottomRowJet
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming normalRadialJet_eq_bottomRowJet → normalRadialJet_eq_bottomRowJet
namespace DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.WeakCutoffSources
namespace WeakFlowCalculus
open MeasureTheory.Measure Filter

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

end WeakFlowCalculus

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

private theorem compact_weighted_flow_bound
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (q : ℝ → X → X) (hq : Continuous (Function.uncurry q))
    (hz : ∀ x, q 0 x = x) (ha : ∀ s t x, q (s+t) x = q t (q s x))
    (χ J dJ : X → ℂ) (hχ : Continuous χ) (hJ : Continuous J) (hdJ : Continuous dJ)
    (hs : HasCompactSupport χ)
    (hderivJ : ∀ x t, HasDerivAt (fun s => J (q s x)) (dJ (q t x)) t)
    (L : ℝ≥0) (hLip : ∀ x, LipschitzOnWith L (fun t => χ (q t x)) (Set.Icc (-1 : ℝ) 1)) :
    ∃ B : X → ℝ, Integrable B μ ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x,
        ‖t⁻¹ • (χ (q t x) * J (q t x) - χ x * J x)‖ ≤ B x := by
  let K := (fun p : ℝ × X => q (-p.1) p.2) '' (Set.Icc (-1 : ℝ) 1 ×ˢ tsupport χ)
  have hK : IsCompact K := (isCompact_Icc.prod hs).image
    (hq.comp (continuous_fst.neg.prodMk continuous_snd))
  let K' := Function.uncurry q '' (Set.Icc (0 : ℝ) 1 ×ˢ K)
  have hK' : IsCompact K' := (isCompact_Icc.prod hK).image hq
  obtain ⟨Mχ, hMχ⟩ := hs.exists_bound_of_continuousOn hχ.continuousOn
  obtain ⟨MJ, hMJ⟩ := hK.exists_bound_of_continuousOn hJ.continuousOn
  obtain ⟨MD, hMD⟩ := hK'.exists_bound_of_continuousOn hdJ.continuousOn
  let C := max 0 Mχ * max 0 MD + (L : ℝ) * max 0 MJ
  let B := K.indicator (fun _ => C)
  have hB : Integrable B μ :=
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  refine ⟨B, hB, ?_⟩
  intro t ht ht1 x
  have htmem : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, ht1⟩
  change _ ≤ K.indicator (fun _ => C) x
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
    have hct : ‖χ (q t x)‖ ≤ max 0 Mχ := by
      by_cases hc : q t x ∈ tsupport χ
      · exact (hMχ _ hc).trans (le_max_right _ _)
      · rw [image_eq_zero_of_notMem_tsupport hc, norm_zero]
        exact le_max_left _ _
    have hcx : ‖χ (q t x) - χ x‖ ≤ (L : ℝ) * t := by
      have h := (hLip x).norm_sub_le htmem
        (show (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 by norm_num)
      simpa only [hz, sub_zero, Real.norm_eq_abs, abs_of_pos ht] using h
    have hd : ∀ s ∈ Set.Ico (0 : ℝ) 1, ‖dJ (q s x)‖ ≤ max 0 MD := by
      intro s hs'
      have hqs : q s x ∈ K' := ⟨(s,x), ⟨Set.Ico_subset_Icc_self hs', hx⟩, rfl⟩
      exact (hMD _ hqs).trans (le_max_right _ _)
    have hj : ‖J (q t x) - J x‖ ≤ max 0 MD * t := by
      have h := norm_image_sub_le_of_norm_deriv_le_segment'
        (fun s _ => (hderivJ x s).hasDerivWithinAt) hd t ⟨ht.le,ht1⟩
      simpa only [hz, sub_zero, mul_one] using h
    have he : χ (q t x) * J (q t x) - χ x * J x =
        χ (q t x) * (J (q t x) - J x) + (χ (q t x) - χ x) * J x := by ring
    have hN : ‖χ (q t x) * J (q t x) - χ x * J x‖ ≤ C * t := by
      rw [he]
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul]
      have hJx : ‖J x‖ ≤ max 0 MJ := (hMJ x hx).trans (le_max_right _ _)
      have h1 := mul_le_mul hct hj (norm_nonneg _) (le_max_left _ _)
      have h2 := mul_le_mul hcx hJx (norm_nonneg _) (by positivity)
      dsimp [C]
      nlinarith
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    exact (mul_le_mul_of_nonneg_left hN (by positivity)).trans_eq (by field_simp)
  · rw [Set.indicator_of_notMem hx]
    have hχx : χ x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hxs
      exact hx ⟨(0,x), ⟨by norm_num, hxs⟩, by simp [hz]⟩
    have hχt : χ (q t x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hts
      apply hx
      refine ⟨(t,q t x), ⟨htmem, hts⟩, ?_⟩
      change q (-t) (q t x) = x
      rw [← ha, add_neg_cancel, hz]
    simp [hχx, hχt]

private theorem weak_flow_integral_zero
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (q : ℝ → X → X) (hq : ∀ t, MeasurePreserving (q t) μ μ)
    (hz : ∀ x, q 0 x = x)
    (f d : X → ℂ) (hf : Integrable f μ)
    (hderiv : ∀ᵐ x ∂μ, HasDerivAt (fun t => f (q t x)) (d x) 0)
    (B : X → ℝ) (hB : Integrable B μ)
    (hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂μ,
      ‖t⁻¹ • (f (q t x) - f x)‖ ≤ B x) :
    (∫ x, d x ∂μ) = 0 := by
  have hmeas : ∀ t : ℝ, AEStronglyMeasurable
      (fun x => t⁻¹ • (f (q t x) - f x)) μ := by
    intro t
    have hqi : Integrable (fun x => f (q t x)) μ :=
      (hq t).integrable_comp_of_integrable hf
    exact (hqi.sub hf).aestronglyMeasurable.const_smul (t⁻¹ : ℝ)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun t : ℝ => t⁻¹ • (f (q t x) - f x))
      (𝓝[>] 0) (𝓝 (d x)) := by
    filter_upwards [hderiv] with x hx
    simpa only [zero_add, hz] using hx.tendsto_slope_zero_right
  have ht := tendsto_integral_filter_of_dominated_convergence B
    (Eventually.of_forall hmeas) hbound hB hlim
  have heq (t : ℝ) :
      (∫ x, t⁻¹ • (f (q t x) - f x) ∂μ) = 0 := by
    have hqi : Integrable (fun x => f (q t x)) μ :=
      (hq t).integrable_comp_of_integrable hf
    have hm := hq t
    have hv := integral_map hm.measurable.aemeasurable
      (show AEStronglyMeasurable f (Measure.map (q t) μ) by
        rw [hm.map_eq]; exact hf.aestronglyMeasurable)
    rw [hm.map_eq] at hv
    rw [integral_smul, integral_sub hqi hf, ← hv, sub_self, smul_zero]
  exact tendsto_nhds_unique (ht.congr' (Eventually.of_forall heq)) tendsto_const_nhds

private theorem weak_ibp_of_integrated_product_derivative
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (χ J dχ dJ : X → ℂ)
    (hf : Integrable (fun x => dχ x * J x + χ x * dJ x) μ)
    (hJ : Integrable (fun x => χ x * dJ x) μ)
    (hzero : (∫ x, dχ x * J x + χ x * dJ x ∂μ) = 0) :
    Integrable (fun x => dχ x * J x) μ ∧
      (∫ x, χ x * dJ x ∂μ) = -(∫ x, dχ x * J x ∂μ) := by
  have hχ : Integrable (fun x => dχ x * J x) μ := by
    convert hf.sub hJ using 1
    ext x
    simp
  refine ⟨hχ, ?_⟩
  rw [integral_add hχ hJ] at hzero
  exact eq_neg_of_add_eq_zero_right hzero

 theorem compact_flow_weak_ibp
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (q : ℝ → X → X) (hq : Continuous (Function.uncurry q))
    (hμ : ∀ t, MeasurePreserving (q t) μ μ)
    (hz : ∀ x, q 0 x = x) (ha : ∀ s t x, q (s+t) x = q t (q s x))
    (χ J dχ dJ : X → ℂ) (hχ : Continuous χ) (hJ : Continuous J) (hdJ : Continuous dJ)
    (hs : HasCompactSupport χ)
    (hderivχ : ∀ᵐ x ∂μ, HasDerivAt (fun t => χ (q t x)) (dχ x) 0)
    (hderivJ : ∀ x t, HasDerivAt (fun s => J (q s x)) (dJ (q t x)) t)
    (L : ℝ≥0) (hLip : ∀ x, LipschitzOnWith L (fun t => χ (q t x)) (Set.Icc (-1 : ℝ) 1)) :
    Integrable (fun x => dχ x * J x) μ ∧
      (∫ x, χ x * dJ x ∂μ) = -(∫ x, dχ x * J x ∂μ) := by
  let f := fun x => χ x * J x
  let d := fun x => dχ x * J x + χ x * dJ x
  have hf : Integrable f μ :=
    (hχ.mul hJ).integrable_of_hasCompactSupport (hs.mul_right)
  have hderiv : ∀ᵐ x ∂μ, HasDerivAt (fun t => f (q t x)) (d x) 0 := by
    filter_upwards [hderivχ] with x hx
    simpa only [d, f, hz, Pi.mul_def] using hx.mul (hderivJ x 0)
  obtain ⟨B,hB,hbound⟩ := compact_weighted_flow_bound μ q hq hz ha
    χ J dJ hχ hJ hdJ hs hderivJ L hLip
  have hbf : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂μ,
      ‖t⁻¹ • (f (q t x) - f x)‖ ≤ B x := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    exact Eventually.of_forall (hbound t ht ht1.le)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun t : ℝ => t⁻¹ • (f (q t x) - f x))
      (𝓝[>] 0) (𝓝 (d x)) := by
    filter_upwards [hderiv] with x hx
    simpa only [zero_add, hz] using hx.tendsto_slope_zero_right
  have hdmeas : AEStronglyMeasurable d μ := by
    apply aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ)) _ hlim
    intro t
    exact (((hμ t).integrable_comp_of_integrable hf).sub hf).aestronglyMeasurable.const_smul
      (t⁻¹ : ℝ)
  have hdint : Integrable d μ := by
    apply hB.mono' hdmeas
    filter_upwards [hlim] with x hx
    apply le_of_tendsto (continuous_norm.continuousAt.tendsto.comp hx)
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    exact hbound t ht ht1.le x
  have hzint := weak_flow_integral_zero μ q hμ hz f d hf hderiv B hB hbf
  exact weak_ibp_of_integrated_product_derivative μ χ J dχ dJ hdint
    ((hχ.mul hdJ).integrable_of_hasCompactSupport hs.mul_right) hzint

 theorem flow_ae_differentiable
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [SFinite μ]
    (q : ℝ → X → X) (hq : Continuous (Function.uncurry q))
    (hμ : ∀ t, MeasurePreserving (q t) μ μ)
    (_hz : ∀ x, q 0 x = x) (ha : ∀ s t x, q (s+t) x = q t (q s x))
    (f : X → ℂ) (hf : Continuous f)
    (L : ℝ≥0) (hLip : ∀ x, LipschitzOnWith L (fun t => f (q t x)) (Set.Icc (-1 : ℝ) 1)) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ (fun t => f (q t x)) 0 := by
  let ν : Measure ℝ := volume.restrict (Set.Ioo (-1 : ℝ) 1)
  have hν : ν Set.univ ≠ 0 := by
    simp [ν, Real.volume_Ioo]
  have hdall : ∀ x, ∀ᵐ t ∂ν, DifferentiableAt ℝ (fun s => f (q s x)) t := by
    intro x
    have hdiff := ((hLip x).mono Set.Ioo_subset_Icc_self).ae_differentiableWithinAt_real
      measurableSet_Ioo
    filter_upwards [hdiff, ae_restrict_mem measurableSet_Ioo] with t ht htm
    exact ht.differentiableAt (isOpen_Ioo.mem_nhds htm)
  have hcont : Continuous (Function.uncurry (fun x t => f (q t x))) := by
    exact hf.comp (hq.comp continuous_swap)
  have hmeas : MeasurableSet {p : X × ℝ | DifferentiableAt ℝ (fun s => f (q s p.1)) p.2} :=
    measurableSet_of_differentiableAt_with_param ℝ hcont
  have hswap : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, DifferentiableAt ℝ (fun s => f (q s x)) t :=
    (Measure.ae_ae_comm hmeas).1 (Eventually.of_forall hdall)
  have hν0 : ν ≠ 0 := fun h => hν (by rw [h]; simp)
  let : (ae ν).NeBot := ae_neBot.mpr hν0
  obtain ⟨t, ht⟩ := hswap.exists
  have hp : MeasurableSet {x : X | DifferentiableAt ℝ (fun s => f (q s x)) 0} := by
    exact hmeas.preimage (measurable_id.prodMk measurable_const)
  have htrans : ∀ᵐ x ∂μ, DifferentiableAt ℝ (fun s => f (q s (q t x))) 0 := by
    filter_upwards [ht] with x hx
    have hh := (show DifferentiableAt ℝ (fun s => f (q s x)) ((0 : ℝ) + t) by simpa using hx).comp 0
      ((differentiableAt_id (x := (0 : ℝ))).add_const t)
    convert hh using 1
    funext s
    simp only [Function.comp_def]
    rw [add_comm, ha]
    rfl
  have hm := hμ t
  have he := ae_map_iff (μ := μ) hm.measurable.aemeasurable hp
  rw [hm.map_eq] at he
  exact he.mpr htrans

 def nativeFlow (w : NumberField.InfinitePlace F) (i : Fin 6)
    (t : ℝ) (x : X F ζ hζ) : X F ζ hζ :=
  KPSmoothActualFlowData.rightTranslate F ζ hζ
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPSmoothActualFlowData.flow F (w,i) t)) x

 theorem nativeFlow_zero (w : NumberField.InfinitePlace F) (i : Fin 6)
    (x : X F ζ hζ) : nativeFlow w i 0 x = x := by
  unfold nativeFlow
  rw [(KPSmoothActualFlowData.flow_properties F (w,i)).1,
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1]
  exact congrFun (KPSmoothQuotientTranslationFlow.rightTranslation_one
    (KPSmoothActualFlowData.rationalSubgroup F ζ hζ)) x

 theorem nativeFlow_add (w : NumberField.InfinitePlace F) (i : Fin 6)
    (s t : ℝ) (x : X F ζ hζ) : nativeFlow w i (s+t) x = nativeFlow w i t (nativeFlow w i s x) := by
  unfold nativeFlow
  rw [(KPSmoothActualFlowData.flow_properties F (w,i)).2.1,
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  exact congrFun (KPSmoothQuotientTranslationFlow.rightTranslation_mul
    (KPSmoothActualFlowData.rationalSubgroup F ζ hζ) _ _) x

section ActualCutoffSupport
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

end ActualCutoffSupport

end DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.WeakCutoffSources

end
