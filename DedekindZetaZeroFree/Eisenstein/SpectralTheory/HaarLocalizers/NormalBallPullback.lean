module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.HaarLocalizers.LineRestriction

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPFixedHaarNormalBallMaps

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualFixedHaarCoreLocalizers KPContSectorSmoothFramesSupport
  KPContSectorLineL2Isometry

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

attribute [local instance 5000] KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line
attribute [local instance 5000] KPContSectorLineL2Isometry.instNormedSpaceL2Line
attribute [local instance 5000] KPContSectorLineL2Isometry.instInnerProductSpaceL2Line

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

private theorem sectionNorm_nonnegative (s : Sections F ζ hζ U R P H) (b : X_U F ζ hζ U) :
    0 ≤ sectionNorm F ζ hζ U R P H s b := by
  let p := (H.atlas U).components.symm b
  obtain ⟨x, hx⟩ := Quotient.mk_surjective p.2
  have he : (H.atlas U).components ⟨p.1, Quotient.mk _ x⟩ = b := by
    rw [hx]; exact (H.atlas U).components.apply_symm_apply b
  rw [← he, sectionNorm_component]
  exact norm_nonneg _

private theorem sectionNorm_memLp (s : BorelL2Sections F ζ hζ U R P H) :
    MemLp (sectionNorm F ζ hζ U R P H s.val) 2 (muU F ζ hζ U R P) ∧
    (eLpNorm (sectionNorm F ζ hζ U R P H s.val) 2 (muU F ζ hζ U R P)).toReal =
      ‖mk F ζ hζ U R P H s‖ := by
  have hm : Measurable (sectionNorm F ζ hζ U R P H s.val) := by
    have he : sectionNorm F ζ hζ U R P H s.val = fun b =>
        Real.sqrt ((squaredNorm F ζ hζ U R P H s.val b).toReal) := by
      funext b
      rw [squaredNorm, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq
        (sectionNorm_nonnegative F ζ hζ U R P H s.val b)]
    rw [he]
    exact (squaredNorm_measurable F ζ hζ U R P H s.val s.property.1).ennreal_toReal.sqrt
  have hq := (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable
  have he : (sectionNorm F ζ hζ U R P H s.val) ∘
      KPContSectorCoveredQuotientVocabulary.q F ζ hζ U =
      fun v => ‖(scalarRepresentative F ζ hζ U R P H s.val).val v‖ := by
    funext v
    have hh := sectionNorm_pullback F ζ hζ U R P H
      (scalarRepresentative F ζ hζ U R P H s.val) v
    rw [scalarRepresentative_eq_symm, (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H).apply_symm_apply] at hh
    exact hh
  have hmmap : AEStronglyMeasurable (sectionNorm F ζ hζ U R P H s.val)
      (Measure.map (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U)
        (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U)) := hm.aestronglyMeasurable
  rw [KPContSectorFixedPushforwardSupport.map_q_coveredMeasure F ζ hζ R P U] at hmmap
  have hi := (representative_memLp F ζ hζ U R P H s).norm
  have hp : MemLp (sectionNorm F ζ hζ U R P H s.val) 2 (muU F ζ hζ U R P) := by
    change MemLp _ 2 (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U)
    rw [← KPContSectorFixedPushforwardSupport.map_q_coveredMeasure F ζ hζ R P U]
    apply (memLp_map_measure_iff hm.aestronglyMeasurable hq.aemeasurable).mpr
    rw [he]
    exact hi
  refine ⟨hp, ?_⟩
  have hh := eLpNorm_map_measure (p := 2)
    (μ := KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U) hm.aestronglyMeasurable hq.aemeasurable
  rw [KPContSectorFixedPushforwardSupport.map_q_coveredMeasure F ζ hζ R P U, he,
    eLpNorm_norm _ (representative_memLp F ζ hζ U R P H s).aestronglyMeasurable] at hh
  change (eLpNorm _ 2 (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U)).toReal = _
  rw [hh]
  change _ = ‖(representative_memLp F ζ hζ U R P H s).toLp _‖
  rw [Lp.norm_def, eLpNorm_congr_ae (representative_memLp F ζ hζ U R P H s).coeFn_toLp]

private theorem actual_lower (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U)) :
    0 < ((H.disintegration U).componentWeight C.component).toReal * C.lower ∧
    ∀ x ∈ closure (Metric.ball (0 : KPCoreChartLocalizers.E C.n) C.radius),
      ((H.disintegration U).componentWeight C.component).toReal * C.lower ≤ actualWeight F ζ hζ U R P H C x := by
  have hw := ENNReal.toReal_pos (ne_of_gt ((H.disintegration U).positive_componentWeight C.component))
    (ne_of_lt ((H.disintegration U).finite_componentWeight C.component))
  refine ⟨mul_pos hw C.positive_lower, ?_⟩
  intro x hx
  exact mul_le_mul_of_nonneg_left (C.finite_bounds x hx).1 hw.le

private theorem chart_volume_le (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U)) :
    volume.restrict (Metric.ball 0 C.radius) ≤
      ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞) *
        (ENNReal.ofReal (((H.disintegration U).componentWeight C.component).toReal * C.lower))⁻¹) •
      ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball 0 C.radius)).withDensity
          (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x))) := by
  have hl := ne_of_gt (ENNReal.ofReal_pos.mpr (actual_lower F ζ hζ U R P H C).1)
  have hh : ENNReal.ofReal (((H.disintegration U).componentWeight C.component).toReal * C.lower) •
      volume.restrict (Metric.ball 0 C.radius) ≤
      (volume.restrict (Metric.ball 0 C.radius)).withDensity
        (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x)) := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact ENNReal.ofReal_le_ofReal ((actual_lower F ζ hζ U R P H C).2 x (subset_closure hx))
  have hh' := smul_le_smul_left
    ((ENNReal.ofReal (((H.disintegration U).componentWeight C.component).toReal * C.lower))⁻¹) hh
  rw [smul_smul, ENNReal.inv_mul_cancel hl ENNReal.ofReal_ne_top, one_smul] at hh'
  rw [smul_smul, mul_right_comm, ENNReal.mul_inv_cancel
    (by simp : (Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞) ≠ 0) (by simp), one_mul]
  exact hh'

private theorem chart_base_measurable (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U)) :
    AEMeasurable (C.toBase F ζ hζ H.totallyComplex U) (volume.restrict (Metric.ball 0 C.radius)) := by
  letI : BorelSpace (X_U F ζ hζ U) := ⟨rfl⟩
  have hc : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative C.component)) := by
    have hh := (H.atlas U).components.continuous.comp (continuous_sigmaMk (i := C.component))
    simpa only [Function.comp_def, (H.atlas U).components_formula] using hh
  have hp : Continuous (KPCuspSiegel.projection F
    (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative C.component))) := continuous_quotient_mk'
  exact ((hc.comp hp).comp_continuousOn (C.smooth_coordinates.continuousOn.mono
    (subset_closure.trans C.closed_ball_in_extension))).aemeasurable Metric.isOpen_ball.measurableSet

private theorem coefficient_norm (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (s : Sections F ζ hζ U R P H) (x : KPCoreChartLocalizers.E C.n) :
    sectionNorm F ζ hζ U R P H s (C.toBase F ζ hζ H.totallyComplex U x) =
      ‖(s C.component).val (C.coordinates x)‖ := by
  rw [KPCoreChartLocalizers.Chart.toBase, ← (H.atlas U).components_formula]
  exact sectionNorm_component F ζ hζ U R P H s C.component (C.coordinates x)

section Pullback
variable (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
variable (hchart : Measure.map (C.toBase F ζ hζ H.totallyComplex U)
    ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
      (volume.restrict (Metric.ball 0 C.radius)).withDensity
        (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x))) =
  (muU F ζ hζ U R P).restrict (C.O F ζ hζ H.totallyComplex U))

 def chartConstant : ℝ≥0∞ :=
  (Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞) *
    (ENNReal.ofReal (((H.disintegration U).componentWeight C.component).toReal * C.lower))⁻¹

private theorem chartConstant_finite : chartConstant F ζ hζ U R P H C ≠ ⊤ :=
  ENNReal.mul_ne_top (by simp) (ENNReal.inv_ne_top.mpr
    (ne_of_gt (ENNReal.ofReal_pos.mpr (actual_lower F ζ hζ U R P H C).1)))

 def chartMeasure : Measure (KPCoreChartLocalizers.E C.n) :=
  (Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
    (volume.restrict (Metric.ball 0 C.radius)).withDensity
      (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x))

 def chartCoefficient (s : BorelL2Sections F ζ hζ U R P H)
    (x : KPCoreChartLocalizers.E C.n) : ℂ := (s.val C.component).val (C.coordinates x)

private theorem chartCoefficient_measurable (s : BorelL2Sections F ζ hζ U R P H) :
    AEStronglyMeasurable (chartCoefficient F ζ hζ U R P H C s)
      (volume.restrict (Metric.ball 0 C.radius)) := by
  have hc : AEMeasurable C.coordinates (volume.restrict (Metric.ball 0 C.radius)) :=
    (C.smooth_coordinates.continuousOn.mono
      (subset_closure.trans C.closed_ball_in_extension)).aemeasurable Metric.isOpen_ball.measurableSet
  exact ((s.property.1 C.component).comp_aemeasurable hc).aestronglyMeasurable

include hchart in
private theorem chartCoefficient_memLp_bound (s : BorelL2Sections F ζ hζ U R P H) :
    MemLp (chartCoefficient F ζ hζ U R P H C s) 2 (volume.restrict (Metric.ball 0 C.radius)) ∧
    eLpNorm (chartCoefficient F ζ hζ U R P H C s) 2 (volume.restrict (Metric.ball 0 C.radius)) ≤
      (chartConstant F ζ hζ U R P H C) ^ (1/2 : ℝ) *
        eLpNorm (sectionNorm F ζ hζ U R P H s.val) 2 (muU F ζ hζ U R P) := by
  let ν := chartMeasure F ζ hζ U R P H C
  have hb : AEMeasurable (C.toBase F ζ hζ H.totallyComplex U) ν :=
    ((chart_base_measurable F ζ hζ U R P H C).mono_ac
      (withDensity_absolutelyContinuous _ _)).smul_measure _
  have hp := (sectionNorm_memLp F ζ hζ U R P H s).1
  have hmap : MemLp (sectionNorm F ζ hζ U R P H s.val) 2
      (Measure.map (C.toBase F ζ hζ H.totallyComplex U) ν) := by
    rw [show Measure.map (C.toBase F ζ hζ H.totallyComplex U) ν = _ from hchart]
    exact hp.restrict _
  have hr := hmap.comp_of_map hb
  have hc := chartCoefficient_measurable F ζ hζ U R P H C s
  have hnorm : ∀ᵐ x ∂ν,
      ‖(sectionNorm F ζ hζ U R P H s.val ∘ C.toBase F ζ hζ H.totallyComplex U) x‖ =
      ‖chartCoefficient F ζ hζ U R P H C s x‖ := by
    filter_upwards [] with x
    dsimp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (sectionNorm_nonnegative F ζ hζ U R P H s.val _)]
    exact coefficient_norm F ζ hζ U R P H C s.val x
  have hν : MemLp (chartCoefficient F ζ hζ U R P H C s) 2 ν :=
    hr.congr_norm ((hc.mono_ac (withDensity_absolutelyContinuous _ _)).smul_measure _) hnorm
  refine ⟨hν.of_measure_le_smul (chartConstant_finite F ζ hζ U R P H C)
    (chart_volume_le F ζ hζ U R P H C), ?_⟩
  have he := eLpNorm_le_of_measure_le_smul
    (f := chartCoefficient F ζ hζ U R P H C s) (p := 2) (chart_volume_le F ζ hζ U R P H C)
  have hnormeq := eLpNorm_congr_norm_ae (p := 2) hr.aestronglyMeasurable hν.aestronglyMeasurable hnorm
  have hmapnorm := eLpNorm_map_measure (p := 2) hmap.aestronglyMeasurable hb
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, ENNReal.smul_def, smul_eq_mul] at he
  change eLpNorm _ 2 (volume.restrict (Metric.ball 0 C.radius)) ≤
    (chartConstant F ζ hζ U R P H C) ^ (1/2 : ℝ) * eLpNorm _ 2 ν at he
  rw [← hnormeq, ← hmapnorm, show Measure.map (C.toBase F ζ hζ H.totallyComplex U) ν = _ from hchart] at he
  exact he.trans (mul_le_mul_right (eLpNorm_mono_measure _ Measure.restrict_le_self) _)

variable (η : KPCoreChartLocalizers.E C.n → ℝ)
variable (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Metric.ball 0 C.radius)
variable (M : ℝ) (hM : 0 ≤ M) (hηM : ∀ x, |η x| ≤ M)

 def cutoffCoefficient (s : BorelL2Sections F ζ hζ U R P H) : KPCoreChartLocalizers.E C.n → ℂ :=
  fun x => (η x : ℂ) * chartCoefficient F ζ hζ U R P H C s x

include hchart hη hηs hηM in
 theorem cutoffCoefficient_memLp_bound (s : BorelL2Sections F ζ hζ U R P H) :
    MemLp (cutoffCoefficient F ζ hζ U R P H C η s) 2
      (volume.restrict (KPCoreChartLocalizers.cube C.n C.a)) ∧
    eLpNorm (cutoffCoefficient F ζ hζ U R P H C η s) 2
      (volume.restrict (KPCoreChartLocalizers.cube C.n C.a)) ≤
      (ENNReal.ofReal M * (chartConstant F ζ hζ U R P H C) ^ (1/2 : ℝ)) *
        eLpNorm (sectionNorm F ζ hζ U R P H s.val) 2 (muU F ζ hζ U R P) := by
  have hb : Metric.ball (0 : KPCoreChartLocalizers.E C.n) C.radius ⊆ KPCoreChartLocalizers.cube C.n C.a :=
    subset_closure.trans (C.closed_ball_in_cube.trans interior_subset)
  have hh := chartCoefficient_memLp_bound F ζ hζ U R P H C hchart s
  have hm : AEStronglyMeasurable (cutoffCoefficient F ζ hζ U R P H C η s)
      (volume.restrict (Metric.ball 0 C.radius)) :=
    ((Complex.ofRealCLM.continuous.comp hη.continuous).measurable.aestronglyMeasurable).mul hh.1.aestronglyMeasurable
  have hn : ∀ᵐ x ∂volume.restrict (Metric.ball 0 C.radius),
      ‖cutoffCoefficient F ζ hζ U R P H C η s x‖ ≤ M * ‖chartCoefficient F ζ hζ U R P H C s x‖ := by
    filter_upwards [] with x
    exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right
      (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hηM x) (norm_nonneg _))
  have hl := hh.1.of_le_mul hm hn
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm hn 2
  have hind : (Metric.ball (0 : KPCoreChartLocalizers.E C.n) C.radius).indicator
      (cutoffCoefficient F ζ hζ U R P H C η s) = cutoffCoefficient F ζ hζ U R P H C η s := by
    funext x
    by_cases hx : x ∈ Metric.ball 0 C.radius
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx]
      simp [cutoffCoefficient, image_eq_zero_of_notMem_tsupport (fun he => hx (hηs he))]
  constructor
  · rw [← hind]
    apply (memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet.nullMeasurableSet).mpr
    rw [Measure.restrict_restrict_of_subset hb]
    exact hl
  · rw [← hind, eLpNorm_indicator_eq_eLpNorm_restrict Metric.isOpen_ball.measurableSet.nullMeasurableSet,
      Measure.restrict_restrict_of_subset hb]
    exact he.trans ((mul_le_mul_right hh.2 (ENNReal.ofReal M)).trans_eq (mul_assoc _ _ _).symm)

include hchart hη hηs hηM in
 def cutoffLinear : BorelL2Sections F ζ hζ U R P H →ₗ[ℂ]
    Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a)) where
  toFun s := (cutoffCoefficient_memLp_bound F ζ hζ U R P H C hchart η hη hηs M hηM s).1.toLp _
  map_add' s t := by
    apply Lp.ext
    filter_upwards [(cutoffCoefficient_memLp_bound F ζ hζ U R P H C hchart η hη hηs M hηM (s+t)).1.coeFn_toLp,
      (cutoffCoefficient_memLp_bound F ζ hζ U R P H C hchart η hη hηs M hηM s).1.coeFn_toLp,
      (cutoffCoefficient_memLp_bound F ζ hζ U R P H C hchart η hη hηs M hηM t).1.coeFn_toLp,
      Lp.coeFn_add ((cutoffCoefficient_memLp_bound F ζ hζ U R P H C hchart η hη hηs M hηM s).1.toLp _)
        ((cutoffCoefficient_memLp_bound F ζ hζ U R P H C hchart η hη hηs M hηM t).1.toLp _)] with x hst hs ht ha
    dsimp only [Pi.add_apply] at ha
    rw [hst, ha, hs, ht]
    simp [cutoffCoefficient, chartCoefficient, mul_add]
  map_smul' c s := by
    apply Lp.ext
    filter_upwards [(cutoffCoefficient_memLp_bound F ζ hζ U R P H C hchart η hη hηs M hηM (c • s)).1.coeFn_toLp,
      (cutoffCoefficient_memLp_bound F ζ hζ U R P H C hchart η hη hηs M hηM s).1.coeFn_toLp,
      Lp.coeFn_smul c ((cutoffCoefficient_memLp_bound F ζ hζ U R P H C hchart η hη hηs M hηM s).1.toLp _)] with x hcs hs hc
    dsimp only [Pi.smul_apply, smul_eq_mul] at hc
    simp only [RingHom.id_apply]
    rw [hcs, hc, hs]
    simp [cutoffCoefficient, chartCoefficient, mul_left_comm, mul_comm, mul_assoc]

include hchart hη hηs hηM hM in
private theorem cutoffLinear_bound (s : BorelL2Sections F ζ hζ U R P H) :
    ‖cutoffLinear F ζ hζ U R P H C hchart η hη hηs M hηM s‖ ≤
      (M * Real.sqrt ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ) /
        (((H.disintegration U).componentWeight C.component).toReal * C.lower))) * ‖mk F ζ hζ U R P H s‖ := by
  have hh := cutoffCoefficient_memLp_bound F ζ hζ U R P H C hchart η hη hηs M hηM s
  have hc : ENNReal.ofReal M * (chartConstant F ζ hζ U R P H C) ^ (1/2 : ℝ) *
      eLpNorm (sectionNorm F ζ hζ U R P H s.val) 2 (muU F ζ hζ U R P) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (chartConstant_finite F ζ hζ U R P H C)))
      (sectionNorm_memLp F ζ hζ U R P H s).1.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono hc hh.2
  change ‖hh.1.toLp _‖ ≤ _
  rw [Lp.norm_def, eLpNorm_congr_ae hh.1.coeFn_toLp]
  refine hreal.trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM,
    ← ENNReal.toReal_rpow, (sectionNorm_memLp F ζ hζ U R P H s).2]
  congr 2
  rw [Real.sqrt_eq_rpow]
  congr 1
  simp only [chartConstant, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal (actual_lower F ζ hζ U R P H C).1.le, div_eq_mul_inv]
end Pullback

theorem chartPullback_exists
    (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (η : KPCoreChartLocalizers.E C.n → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Metric.ball 0 C.radius)
    (hηinv : ∀ (g : C.G F ζ hζ H.totallyComplex U) x, η (C.orthogonal g x) = η x)
    (M : ℝ) (hM : 0 ≤ M) (hηM : ∀ x, |η x| ≤ M)
    (hchart : Measure.map (C.toBase F ζ hζ H.totallyComplex U)
        ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
          (volume.restrict (Metric.ball 0 C.radius)).withDensity
            (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x))) =
      (muU F ζ hζ U R P).restrict (C.O F ζ hζ H.totallyComplex U)) :
    ∃ T : H_U F ζ hζ U R →L[ℂ]
        Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a)),
      ‖T‖ ≤ M * Real.sqrt ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ) /
        (((H.disintegration U).componentWeight C.component).toReal * C.lower)) ∧
      ∀ (u : H_U F ζ hζ U R) (s : BorelL2Sections F ζ hζ U R P H),
        sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s →
        T u =ᵐ[volume.restrict (KPCoreChartLocalizers.cube C.n C.a)]
          fun x => (η x : ℂ) * (s.val C.component).val (C.coordinates x) := by
  let B := M * Real.sqrt ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ) /
    (((H.disintegration U).componentWeight C.component).toReal * C.lower))
  have hB : 0 ≤ B := mul_nonneg hM (Real.sqrt_nonneg _)
  let L := cutoffLinear F ζ hζ U R P H C hchart η hη hηs M hηM
  have hL : ∀ s : BorelL2Sections F ζ hζ U R P H,
      ‖L s‖ ≤ B * ‖mk F ζ hζ U R P H s‖ :=
    cutoffLinear_bound F ζ hζ U R P H C hchart η hη hηs M hM hηM
  have hker : nullSections F ζ hζ U R P H ≤ L.ker := by
    intro s hs
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    have hz : mk F ζ hζ U R P H s = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).mpr hs
    have hh := hL s
    rw [hz, norm_zero, mul_zero] at hh
    exact le_antisymm hh (norm_nonneg _)
  let Q : L2Line F ζ hζ U R P H →ₗ[ℂ]
      Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a)) :=
    @Submodule.liftQ ℂ (BorelL2Sections F ζ hζ U R P H)
      inferInstance inferInstance inferInstance (nullSections F ζ hζ U R P H)
      ℂ _ inferInstance inferInstance inferInstance (RingHom.id ℂ) L hker
  have hQmk (s : BorelL2Sections F ζ hζ U R P H) :
      Q (mk F ζ hζ U R P H s) = L s := by
    exact Submodule.liftQ_apply _ _ s
  have hQ : ∀ v : L2Line F ζ hζ U R P H, ‖Q v‖ ≤ B * ‖v‖ := by
    intro v
    obtain ⟨s, hs⟩ := Quotient.exists_rep v
    change mk F ζ hζ U R P H s = v at hs
    rw [← hs, hQmk]
    exact hL s
  let Tlin := Q.comp (sectorLineIsometry F ζ hζ U R P H).toLinearMap
  have hT : ∀ u : H_U F ζ hζ U R, ‖Tlin u‖ ≤ B * ‖u‖ := by
    intro u
    exact (hQ ((sectorLineIsometry F ζ hζ U R P H) u)).trans_eq
      (congrArg (B * ·) ((sectorLineIsometry F ζ hζ U R P H).norm_map u))
  let T := Tlin.mkContinuous B hT
  refine ⟨T, Tlin.mkContinuous_norm_le hB hT, ?_⟩
  · intro u s hs
    have he : T u = L s := by
      change Q ((sectorLineIsometry F ζ hζ U R P H) u) = L s
      rw [hs, hQmk]
    rw [he]
    exact (cutoffCoefficient_memLp_bound F ζ hζ U R P H C hchart η hη hηs M hηM s).1.coeFn_toLp

end DedekindZetaZeroFree.KPFixedHaarNormalBallMaps

end
