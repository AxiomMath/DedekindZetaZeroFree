module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.SmoothPartitions

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.CoreChartLocalizers

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

 instance subsingletonLp {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] [Subsingleton E] {p : ℝ≥0∞} : Subsingleton (Lp E p μ) :=
  ⟨fun f g => Lp.ext (Filter.Eventually.of_forall fun _ => Subsingleton.elim _ _)⟩

private theorem bounded_local_operators_rank_zero
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (hK : MeasurableSet K) (C : FiniteCutoffs F ζ hζ hF U A K)
    (P : FrameComparison F ζ hζ hF U A M C) (hV : V F ζ hζ U = ⊥) :
    Nonempty (LocalOperators F ζ hζ hF U A M C P) := by
  haveI : Subsingleton (V F ζ hζ U) := by rw [hV]; infer_instance
  haveI : Subsingleton (H F ζ hζ hF U A) := inferInstance
  haveI : Subsingleton (HK F ζ hζ hF U A K) := inferInstance
  exact ⟨{
    T := fun _ => 0
    T_formula := fun i v => by
      rw [ContinuousLinearMap.zero_apply]
      refine (Lp.coeFn_zero ℂ 2
        (volume.restrict (cube (C.chart i).n (C.chart i).a))).trans ?_
      filter_upwards with x
      have hv : v ((C.chart i).toBase F ζ hζ hF U x) = 0 := Subsingleton.elim _ _
      by_cases hxb : x ∈ Metric.ball 0 (C.chart i).radius
      · rw [Set.indicator_of_mem hxb, hv]; simp
      · rw [Set.indicator_of_notMem hxb]; rfl
    R := fun _ => 0
    R_formula := fun i f => by
      filter_upwards with x _
      exact Subsingleton.elim _ _
    R_zero_extension := fun i f => by
      filter_upwards with x _
      exact Subsingleton.elim _ _
    smooth_core_image := fun i _ _ =>
      ⟨0, contDiff_const, HasCompactSupport.zero, by simp [tsupport], by
        rw [ContinuousLinearMap.zero_apply]
        exact Lp.coeFn_zero ℂ 2
          (volume.restrict (cube (C.chart i).n (C.chart i).a))⟩ }⟩

theorem chartMeasure_pullback_ae (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    {K : Set (X F ζ hζ U)} (C : FiniteCutoffs F ζ hζ hF U A K) (i : Fin C.count)
    {p : X F ζ hζ U → Prop}
    (hp : ∀ᵐ x ∂quotientMeasure F ζ hζ hF U A, p x) :
    ∀ᵐ x ∂volume.restrict (Metric.ball 0 (C.chart i).radius),
      p ((C.chart i).toBase F ζ hζ hF U x) := by
  letI : BorelSpace (X F ζ hζ U) := ⟨rfl⟩
  have hc : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U
      (A.representative (C.chart i).component)) := by
    have hh := A.components.continuous.comp (continuous_sigmaMk (i := (C.chart i).component))
    simpa only [Function.comp_def, A.components_formula] using hh
  have hproj : Continuous (KPCuspSiegel.projection F
      (KPCuspGenuineMonodromy.Component F ζ hζ U
        (A.representative (C.chart i).component))) :=
    continuous_quot_mk
  have hb := ((hc.comp hproj).comp_continuousOn
    ((C.chart i).smooth_coordinates.continuousOn.mono
      (Set.Subset.trans subset_closure (C.chart i).closed_ball_in_extension))).aemeasurable
        Metric.isOpen_ball.measurableSet (μ := volume)
  have hw := ((C.chart i).smooth_weight.continuousOn.mono
    (Set.Subset.trans subset_closure (C.chart i).closed_ball_in_extension)).aemeasurable
      Metric.isOpen_ball.measurableSet (μ := volume)
  have hd := hb.mono_ac (withDensity_absolutelyContinuous _
    (fun x => ENNReal.ofReal ((C.chart i).weight x)))
  have hmap := ae_restrict_of_ae hp (s := (C.chart i).O F ζ hζ hF U)
  rw [← C.chart_measure i] at hmap
  have hpull := ae_of_ae_map (hd.smul_measure _) hmap
  have hn : (Fintype.card ((C.chart i).G F ζ hζ hF U) : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hh := (Measure.ae_ennreal_smul_measure_iff hn).mp hpull
  have hpos := (ae_withDensity_iff' (hw.ennreal_ofReal)).mp hh
  filter_upwards [hpos, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hball
  apply hx
  exact ne_of_gt (ENNReal.ofReal_pos.mpr
    (lt_of_lt_of_le (C.chart i).positive_lower
      ((C.chart i).finite_bounds x (subset_closure hball)).1))

theorem chartMeasure_volume_le (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (D : Chart F ζ hζ hF U A) :
    volume.restrict (Metric.ball 0 D.radius) ≤
      ((Fintype.card (D.G F ζ hζ hF U) : ℝ≥0∞) * (ENNReal.ofReal D.lower)⁻¹) •
      ((Fintype.card (D.G F ζ hζ hF U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball 0 D.radius)).withDensity
          (fun x => ENNReal.ofReal (D.weight x))) := by
  have hl : ENNReal.ofReal D.lower ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr D.positive_lower)
  have h : (ENNReal.ofReal D.lower) • volume.restrict (Metric.ball 0 D.radius) ≤
      (volume.restrict (Metric.ball 0 D.radius)).withDensity
          (fun x => ENNReal.ofReal (D.weight x)) := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact ENNReal.ofReal_le_ofReal (D.finite_bounds x (subset_closure hx)).1
  have h' := smul_le_smul_left ((ENNReal.ofReal D.lower)⁻¹) h
  rw [smul_smul, ENNReal.inv_mul_cancel hl ENNReal.ofReal_ne_top, one_smul] at h'
  rw [smul_smul, mul_right_comm, ENNReal.mul_inv_cancel
    (by simp : (Fintype.card (D.G F ζ hζ hF U) : ℝ≥0∞) ≠ 0) (by simp), one_mul]
  exact h'

private theorem chart_toBase_aemeasurable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (D : Chart F ζ hζ hF U A) :
    AEMeasurable (D.toBase F ζ hζ hF U) (volume.restrict (Metric.ball 0 D.radius)) := by
  letI : BorelSpace (X F ζ hζ U) := ⟨rfl⟩
  have hc : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U
      (A.representative D.component)) := by
    have hh := A.components.continuous.comp (continuous_sigmaMk (i := D.component))
    simpa only [Function.comp_def, A.components_formula] using hh
  have hproj : Continuous (KPCuspSiegel.projection F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative D.component))) :=
    continuous_quot_mk
  exact ((hc.comp hproj).comp_continuousOn
    (D.smooth_coordinates.continuousOn.mono
      (Set.Subset.trans subset_closure D.closed_ball_in_extension))).aemeasurable
        Metric.isOpen_ball.measurableSet (μ := volume)

theorem chart_pullback_memLp (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    {K : Set (X F ζ hζ U)} (C : FiniteCutoffs F ζ hζ hF U A K) (i : Fin C.count)
    (v : H F ζ hζ hF U A) :
    MemLp (fun x => (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ)) 2
      (volume.restrict (Metric.ball 0 (C.chart i).radius)) := by
  let D := C.chart i
  let ν := (Fintype.card (D.G F ζ hζ hF U) : ℝ≥0∞)⁻¹ •
    (volume.restrict (Metric.ball 0 D.radius)).withDensity
      (fun x => ENNReal.ofReal (D.weight x))
  have hb : AEMeasurable (D.toBase F ζ hζ hF U) ν :=
    ((chart_toBase_aemeasurable F ζ hζ hF U A D).mono_ac
      (withDensity_absolutelyContinuous _ _)).smul_measure _
  have hv : MemLp (fun x => (v x : ℂ)) 2 (quotientMeasure F ζ hζ hF U A) :=
    (V F ζ hζ U).subtypeL.comp_memLp' (Lp.memLp v)
  have hp : MemLp (fun x => (v (D.toBase F ζ hζ hF U x) : ℂ)) 2 ν := by
    have hh := hv.restrict (s := D.O F ζ hζ hF U)
    rw [← C.chart_measure i] at hh
    exact hh.comp_of_map hb
  exact hp.of_measure_le_smul
    (ENNReal.mul_ne_top (by simp)
      (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr D.positive_lower))))
    (chartMeasure_volume_le F ζ hζ hF U A D)

 def cutoffLiftFunction (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (v : H F ζ hζ hF U A) : E (C.chart i).n → ℂ :=
  (Metric.ball 0 (C.chart i).radius).indicator (fun x =>
    (C.phi i ((C.chart i).toBase F ζ hζ hF U x) : ℂ) * (P.phase i x : ℂ) *
      (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ))

 theorem cutoffLiftFunction_memLp (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (v : H F ζ hζ hF U A) :
    MemLp (cutoffLiftFunction F ζ hζ hF U A M C P i v) 2
      (volume.restrict (cube (C.chart i).n (C.chart i).a)) := by
  let D := C.chart i
  have hball : Metric.ball (0 : E D.n) D.radius ⊆ cube D.n D.a :=
    Set.Subset.trans subset_closure (Set.Subset.trans D.closed_ball_in_cube interior_subset)
  apply (memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet.nullMeasurableSet).mpr
  rw [Measure.restrict_restrict_of_subset hball]
  have hv := chart_pullback_memLp F ζ hζ hF U A C i v
  have hc : AEStronglyMeasurable (fun x => (C.cutoff i x : ℂ))
      (volume.restrict (Metric.ball 0 D.radius)) :=
    (Complex.continuous_ofReal.comp (C.smooth_cutoff i).continuous).aestronglyMeasurable
  have hphase : AEStronglyMeasurable (fun x => (P.phase i x : ℂ))
      (volume.restrict (Metric.ball 0 D.radius)) :=
    ((comap_measurable _ : Measurable (Units.val : ℂˣ → ℂ)).comp
      (P.measurable_phase i)).aestronglyMeasurable
  obtain ⟨B, hB⟩ := (C.compact_cutoff i).exists_bound_of_continuous (C.smooth_cutoff i).continuous
  have hh : MemLp (fun x => (C.cutoff i x : ℂ) * (P.phase i x : ℂ) *
      (v (D.toBase F ζ hζ hF U x) : ℂ)) 2 (volume.restrict (Metric.ball 0 D.radius)) := by
    apply hv.of_le_mul (c := B) ((hc.mul hphase).mul hv.aestronglyMeasurable)
    filter_upwards with x
    simpa only [Pi.mul_apply, norm_mul, P.unitary_phase, Complex.norm_real, Real.norm_eq_abs, mul_one] using
      mul_le_mul_of_nonneg_right (hB x) (norm_nonneg (v (D.toBase F ζ hζ hF U x) : ℂ))
  apply hh.ae_eq
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  rw [C.cutoff_formula, Set.indicator_of_mem hx]

theorem chart_pullback_eLpNorm_le (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    {K : Set (X F ζ hζ U)} (C : FiniteCutoffs F ζ hζ hF U A K) (i : Fin C.count)
    (v : H F ζ hζ hF U A) :
    eLpNorm (fun x => (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ)) 2
      (volume.restrict (Metric.ball 0 (C.chart i).radius)) ≤
      ((Fintype.card ((C.chart i).G F ζ hζ hF U) : ℝ≥0∞) *
        (ENNReal.ofReal (C.chart i).lower)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal *
          eLpNorm v 2 (quotientMeasure F ζ hζ hF U A) := by
  let D := C.chart i
  let ν := (Fintype.card (D.G F ζ hζ hF U) : ℝ≥0∞)⁻¹ •
    (volume.restrict (Metric.ball 0 D.radius)).withDensity
      (fun x => ENNReal.ofReal (D.weight x))
  have hb : AEMeasurable (D.toBase F ζ hζ hF U) ν :=
    ((chart_toBase_aemeasurable F ζ hζ hF U A D).mono_ac
      (withDensity_absolutelyContinuous _ _)).smul_measure _
  have hv : MemLp (fun x => (v x : ℂ)) 2 (quotientMeasure F ζ hζ hF U A) :=
    (V F ζ hζ U).subtypeL.comp_memLp' (Lp.memLp v)
  have hm : AEStronglyMeasurable (fun x => (v x : ℂ))
      (Measure.map (D.toBase F ζ hζ hF U) ν) := by
    rw [C.chart_measure i]
    exact hv.aestronglyMeasurable.restrict
  have h := eLpNorm_le_of_measure_le_smul (f := fun x => (v (D.toBase F ζ hζ hF U x) : ℂ))
    (p := 2) (chartMeasure_volume_le F ζ hζ hF U A D)
  change eLpNorm (fun x => (v (D.toBase F ζ hζ hF U x) : ℂ)) 2
    (volume.restrict (Metric.ball 0 D.radius)) ≤
    ((Fintype.card (D.G F ζ hζ hF U) : ℝ≥0∞) * (ENNReal.ofReal D.lower)⁻¹) ^
      (1 / (2 : ℝ≥0∞)).toReal *
      eLpNorm (fun x => (v (D.toBase F ζ hζ hF U x) : ℂ)) 2 ν at h
  have heq := eLpNorm_map_measure (p := 2) hm hb
  simp only [Function.comp_def] at heq
  rw [← heq] at h
  rw [C.chart_measure i] at h
  refine h.trans (mul_le_mul_right ?_ _)
  refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans_eq ?_
  exact eLpNorm_congr_norm_ae hv.aestronglyMeasurable (Lp.aestronglyMeasurable v)
    (Filter.Eventually.of_forall fun x => rfl)

private theorem cutoffLiftFunction_eLpNorm_le (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) {B : ℝ} (hB : ∀ x, ‖C.cutoff i x‖ ≤ B) (v : H F ζ hζ hF U A) :
    eLpNorm (cutoffLiftFunction F ζ hζ hF U A M C P i v) 2
      (volume.restrict (cube (C.chart i).n (C.chart i).a)) ≤
    (ENNReal.ofReal B * ((Fintype.card ((C.chart i).G F ζ hζ hF U) : ℝ≥0∞) *
        (ENNReal.ofReal (C.chart i).lower)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal) *
      eLpNorm v 2 (quotientMeasure F ζ hζ hF U A) := by
  let D := C.chart i
  have hball : Metric.ball (0 : E D.n) D.radius ⊆ cube D.n D.a :=
    Set.Subset.trans subset_closure (Set.Subset.trans D.closed_ball_in_cube interior_subset)
  have hl := (cutoffLiftFunction_memLp F ζ hζ hF U A M C P i v).aestronglyMeasurable
  have hh := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (c := B) hl
    (g := (Metric.ball 0 D.radius).indicator (fun x => (v (D.toBase F ζ hζ hF U x) : ℂ))) ?_ 2
  · rw [eLpNorm_indicator_eq_eLpNorm_restrict Metric.isOpen_ball.measurableSet.nullMeasurableSet,
      Measure.restrict_restrict_of_subset hball] at hh
    refine hh.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_right (chart_pullback_eLpNorm_le F ζ hζ hF U A C i v) _
  · filter_upwards with x
    dsimp [cutoffLiftFunction, D]
    by_cases hx : x ∈ Metric.ball 0 (C.chart i).radius
    · simp only [cutoffLiftFunction, Set.indicator_of_mem hx, norm_mul, P.unitary_phase, mul_one]
      have hc : C.cutoff i x = C.phi i (D.toBase F ζ hζ hF U x) := by
        rw [C.cutoff_formula, Set.indicator_of_mem hx]
      rw [← hc]
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right (hB x) (norm_nonneg (v (D.toBase F ζ hζ hF U x) : ℂ))
    · simp [cutoffLiftFunction, Set.indicator_of_notMem hx]

 def cutoffLiftLinear (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) : H F ζ hζ hF U A →ₗ[ℂ]
      Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a)) where
  toFun v := (cutoffLiftFunction_memLp F ζ hζ hF U A M C P i v).toLp _
  map_add' v w := by
    apply Lp.ext
    refine ((cutoffLiftFunction_memLp F ζ hζ hF U A M C P i (v + w)).coeFn_toLp).trans ?_
    apply Filter.EventuallyEq.trans _ (Lp.coeFn_add _ _).symm
    have hp := chartMeasure_pullback_ae F ζ hζ hF U A C i (Lp.coeFn_add v w)
    have hi : (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius).indicator
        (fun x => ((v + w) ((C.chart i).toBase F ζ hζ hF U x))) =ᵐ[
        volume.restrict (cube (C.chart i).n (C.chart i).a)]
        (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius).indicator
        (fun x => v ((C.chart i).toBase F ζ hζ hF U x) + w ((C.chart i).toBase F ζ hζ hF U x)) :=
      (ae_eq_restrict_iff_indicator_ae_eq Metric.isOpen_ball.measurableSet).mp (by
        rw [Measure.restrict_restrict_of_subset
          (Set.Subset.trans subset_closure (Set.Subset.trans (C.chart i).closed_ball_in_cube interior_subset))]
        exact hp)
    filter_upwards [hi,
      (cutoffLiftFunction_memLp F ζ hζ hF U A M C P i v).coeFn_toLp,
      (cutoffLiftFunction_memLp F ζ hζ hF U A M C P i w).coeFn_toLp] with x hx hv hw
    simp only [Pi.add_apply]
    rw [hv, hw]
    by_cases hxb : x ∈ Metric.ball 0 (C.chart i).radius
    · simp only [Set.indicator_of_mem hxb] at hx
      simp only [cutoffLiftFunction, Set.indicator_of_mem hxb]
      rw [hx]
      simp only [Submodule.coe_add, mul_add]
    · simp [cutoffLiftFunction, Set.indicator_of_notMem hxb]
  map_smul' c v := by
    apply Lp.ext
    refine ((cutoffLiftFunction_memLp F ζ hζ hF U A M C P i (c • v)).coeFn_toLp).trans ?_
    apply Filter.EventuallyEq.trans _ (Lp.coeFn_smul _ _).symm
    have hp := chartMeasure_pullback_ae F ζ hζ hF U A C i (Lp.coeFn_smul c v)
    have hi : (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius).indicator
        (fun x => ((c • v) ((C.chart i).toBase F ζ hζ hF U x))) =ᵐ[
        volume.restrict (cube (C.chart i).n (C.chart i).a)]
        (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius).indicator
        (fun x => c • v ((C.chart i).toBase F ζ hζ hF U x)) :=
      (ae_eq_restrict_iff_indicator_ae_eq Metric.isOpen_ball.measurableSet).mp (by
        rw [Measure.restrict_restrict_of_subset
          (Set.Subset.trans subset_closure (Set.Subset.trans (C.chart i).closed_ball_in_cube interior_subset))]
        exact hp)
    filter_upwards [hi, (cutoffLiftFunction_memLp F ζ hζ hF U A M C P i v).coeFn_toLp] with x hx hv
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [hv]
    by_cases hxb : x ∈ Metric.ball 0 (C.chart i).radius
    · simp only [Set.indicator_of_mem hxb] at hx
      simp [cutoffLiftFunction, Set.indicator_of_mem hxb, hx, mul_left_comm]
    · simp [cutoffLiftFunction, Set.indicator_of_notMem hxb]

 theorem cutoffLiftLinear_bound (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) {B : ℝ} (hB : ∀ x, ‖C.cutoff i x‖ ≤ B) (v : H F ζ hζ hF U A) :
    ‖cutoffLiftLinear F ζ hζ hF U A M C P i v‖ ≤
      (B * ((Fintype.card ((C.chart i).G F ζ hζ hF U) : ℝ≥0∞) *
        (ENNReal.ofReal (C.chart i).lower)⁻¹).toReal ^ (1 / (2 : ℝ≥0∞)).toReal) * ‖v‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg (C.cutoff i 0)).trans (hB 0)
  change ‖(cutoffLiftFunction_memLp F ζ hζ hF U A M C P i v).toLp _‖ ≤ _
  rw [Lp.norm_def, eLpNorm_congr_ae (cutoffLiftFunction_memLp F ζ hζ hF U A M C P i v).coeFn_toLp]
  have hh := ENNReal.toReal_mono (b :=
    (ENNReal.ofReal B * ((Fintype.card ((C.chart i).G F ζ hζ hF U) : ℝ≥0∞) *
      (ENNReal.ofReal (C.chart i).lower)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal) *
    eLpNorm v 2 (quotientMeasure F ζ hζ hF U A)) ?_ (cutoffLiftFunction_eLpNorm_le F ζ hζ hF U A M C P i hB v)
  · simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hB0, Lp.norm_def] using hh
  · apply ENNReal.mul_ne_top _ (Lp.eLpNorm_ne_top v)
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
    exact ENNReal.mul_ne_top (by simp) (ENNReal.inv_ne_top.mpr
      (ne_of_gt (ENNReal.ofReal_pos.mpr (C.chart i).positive_lower)))

 def cutoffLiftMap (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) : H F ζ hζ hF U A →L[ℂ]
      Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a)) := by
  let h := (C.compact_cutoff i).exists_bound_of_continuous (C.smooth_cutoff i).continuous
  refine LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := H F ζ hζ hF U A)
    (F := Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a))) (cutoffLiftLinear F ζ hζ hF U A M C P i)
    (h.choose * ((Fintype.card ((C.chart i).G F ζ hζ hF U) : ℝ≥0∞) *
      (ENNReal.ofReal (C.chart i).lower)⁻¹).toReal ^ (1 / (2 : ℝ≥0∞)).toReal) ?_
  exact cutoffLiftLinear_bound F ζ hζ hF U A M C P i h.choose_spec

private theorem cutoffLiftMap_formula (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (v : H F ζ hζ hF U A) :
    cutoffLiftMap F ζ hζ hF U A M C P i v =ᵐ[
      volume.restrict (cube (C.chart i).n (C.chart i).a)]
      cutoffLiftFunction F ζ hζ hF U A M C P i v :=
  (cutoffLiftFunction_memLp F ζ hζ hF U A M C P i v).coeFn_toLp

private theorem cutoffLiftMap_smooth_core (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (v : H F ζ hζ hF U A) (hv : v ∈ core F ζ hζ hF U A M) :
    ∃ f : E (C.chart i).n → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ interior (cube (C.chart i).n (C.chart i).a) ∧
      cutoffLiftMap F ζ hζ hF U A M C P i v =ᵐ[
        volume.restrict (cube (C.chart i).n (C.chart i).a)] f := by
  obtain ⟨s, hs, hcomp, hvs⟩ := hv
  let D := C.chart i
  let f : E D.n → ℂ := fun x => (C.cutoff i x : ℂ) *
    s.val (D.coordinates x, A.representative D.component)
  have hcut : ContDiff ℝ (⊤ : ℕ∞) (fun x => (C.cutoff i x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (C.smooth_cutoff i)
  have hsupport : tsupport f ⊆ tsupport (C.cutoff i) :=
    Set.Subset.trans tsupport_mul_subset_left (by
      apply tsupport_comp_subset (g := fun x : ℝ => (x : ℂ))
      rfl)
  refine ⟨f, ?_, ?_, Set.Subset.trans hsupport
    (Set.Subset.trans (C.support_cutoff i)
      (Set.Subset.trans subset_closure D.closed_ball_in_cube)), ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport (C.cutoff i)
    · have hxe : x ∈ D.extendedDomain := D.closed_ball_in_extension
        (subset_closure (C.support_cutoff i hx))
      exact hcut.contDiffAt.mul ((hs D.component).contDiffAt.comp x
        (D.smooth_coordinates.contDiffAt (D.open_extendedDomain.mem_nhds hxe)))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [f, hy]
  · exact (C.compact_cutoff i).of_isClosed_subset (isClosed_tsupport f) hsupport
  · refine (cutoffLiftMap_formula F ζ hζ hF U A M C P i v).trans ?_
    have hp := chartMeasure_pullback_ae F ζ hζ hF U A C i hvs
    have hf := P.frame_comparison i s
    have hball := Set.Subset.trans subset_closure
      (Set.Subset.trans D.closed_ball_in_cube interior_subset)
    have heq : cutoffLiftFunction F ζ hζ hF U A M C P i v =ᵐ[
        volume.restrict (Metric.ball 0 D.radius)] f := by
      filter_upwards [hp, hf, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hfx hxb
      change x ∈ Metric.ball 0 (C.chart i).radius at hxb
      simp only [cutoffLiftFunction, Set.indicator_of_mem hxb]
      dsimp only [f]
      rw [C.cutoff_formula, Set.indicator_of_mem hxb, hfx, hx, mul_assoc]
    have heq' : cutoffLiftFunction F ζ hζ hF U A M C P i v =ᵐ[
        (volume.restrict (cube D.n D.a)).restrict (Metric.ball 0 D.radius)] f := by
      rw [Measure.restrict_restrict_of_subset hball]
      exact heq
    have hh := (ae_eq_restrict_iff_indicator_ae_eq Metric.isOpen_ball.measurableSet).mp heq'
    have hsupp : Function.support f ⊆ Metric.ball 0 (C.chart i).radius :=
      Set.Subset.trans (subset_tsupport f) (Set.Subset.trans hsupport (C.support_cutoff i))
    dsimp only [D] at hh
    simpa only [cutoffLiftFunction, Set.indicator_indicator, Set.inter_self,
      Set.indicator_eq_self.mpr hsupp] using hh

theorem bounded_cutoff_lifting
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K)
    (P : FrameComparison F ζ hζ hF U A M C) :
    ∃ T : ∀ i, H F ζ hζ hF U A →L[ℂ]
        Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a)),
      (∀ i v, T i v =ᵐ[volume.restrict (cube (C.chart i).n (C.chart i).a)]
        (Metric.ball 0 (C.chart i).radius).indicator (fun x =>
          (C.phi i ((C.chart i).toBase F ζ hζ hF U x) : ℂ) * (P.phase i x : ℂ) *
            (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ))) ∧
      (∀ i v, v ∈ core F ζ hζ hF U A M →
        ∃ f : E (C.chart i).n → ℂ,
          ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
          tsupport f ⊆ interior (cube (C.chart i).n (C.chart i).a) ∧
          T i v =ᵐ[volume.restrict (cube (C.chart i).n (C.chart i).a)] f) :=
  ⟨cutoffLiftMap F ζ hζ hF U A M C P,
    cutoffLiftMap_formula F ζ hζ hF U A M C P,
    cutoffLiftMap_smooth_core F ζ hζ hF U A M C P⟩

theorem chart_orthogonal_measurePreserving (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (D : Chart F ζ hζ hF U A) (g : D.G F ζ hζ hF U) :
    MeasurePreserving (D.orthogonal g)
      (volume.restrict (Metric.ball (0 : E D.n) D.radius))
      (volume.restrict (Metric.ball (0 : E D.n) D.radius)) := by
  have he : (D.orthogonal g) ⁻¹' Metric.ball (0 : E D.n) D.radius = Metric.ball (0 : E D.n) D.radius := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right,
      LinearIsometryEquiv.norm_map]
  have hr := (LinearIsometryEquiv.measurePreserving (D.orthogonal g)).restrict_preimage
    (s := Metric.ball (0 : E D.n) D.radius) Metric.isOpen_ball.measurableSet
  rw [he] at hr
  exact hr

private theorem chart_rho_norm (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (D : Chart F ζ hζ hF U A) (g : D.G F ζ hζ hF U) :
    ‖(D.rho F ζ hζ hF U g : ℂ)‖ = 1 := by
  exact (((Units.coeHom ℂ).comp (D.rho F ζ hζ hF U)).isOfFinOrder
    (isOfFinOrder_of_finite g)).norm_eq_one

 def chartAverageBall (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (D : Chart F ζ hζ hF U A) :
    Lp ℂ 2 (volume.restrict (Metric.ball (0 : E D.n) D.radius)) →L[ℂ]
      Lp ℂ 2 (volume.restrict (Metric.ball (0 : E D.n) D.radius)) :=
  (Fintype.card (D.G F ζ hζ hF U) : ℂ)⁻¹ •
    ∑ g : D.G F ζ hζ hF U, (((D.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) •
      (Lp.compMeasurePreservingₗᵢ ℂ (D.orthogonal g)
        (chart_orthogonal_measurePreserving F ζ hζ hF U A D g)).toContinuousLinearMap

private theorem chartAverageBall_formula (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (D : Chart F ζ hζ hF U A)
    (f : Lp ℂ 2 (volume.restrict (Metric.ball (0 : E D.n) D.radius))) :
    chartAverageBall F ζ hζ hF U A D f =ᵐ[volume.restrict (Metric.ball (0 : E D.n) D.radius)]
      D.average F ζ hζ hF U f := by
  let c : ℂ := (Fintype.card (D.G F ζ hζ hF U) : ℂ)⁻¹
  let t : D.G F ζ hζ hF U → Lp ℂ 2 (volume.restrict (Metric.ball (0 : E D.n) D.radius)) := fun g =>
    (((D.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) •
      Lp.compMeasurePreserving (D.orthogonal g)
        (chart_orthogonal_measurePreserving F ζ hζ hF U A D g) f
  have ht : ∀ g, t g =ᵐ[volume.restrict (Metric.ball (0 : E D.n) D.radius)] fun x =>
      (((D.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) * f (D.orthogonal g x) := by
    intro g
    filter_upwards [Lp.coeFn_smul (((D.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ)
      (Lp.compMeasurePreserving (D.orthogonal g)
        (chart_orthogonal_measurePreserving F ζ hζ hF U A D g) f),
      Lp.coeFn_compMeasurePreserving f
        (chart_orthogonal_measurePreserving F ζ hζ hF U A D g)] with x h₁ h₂
    simp only [t, h₁, Pi.smul_apply, smul_eq_mul, Function.comp_apply, h₂]
  simp only [chartAverageBall, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  change (c • ∑ g, t g) =ᵐ[volume.restrict (Metric.ball (0 : E D.n) D.radius)] _
  filter_upwards [Lp.coeFn_smul c (∑ g, t g), Lp.coeFn_finsetSum Finset.univ t,
    Filter.eventually_all.mpr ht, ae_restrict_mem Metric.isOpen_ball.measurableSet]
      with x hc hs hx hxb
  rw [hc]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Chart.average,
    Set.indicator_of_mem hxb]
  congr 1
  exact Finset.sum_congr rfl (fun g _ => hx g)

private theorem chartAverageBall_bound (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (D : Chart F ζ hζ hF U A)
    (f : Lp ℂ 2 (volume.restrict (Metric.ball (0 : E D.n) D.radius))) :
    ‖chartAverageBall F ζ hζ hF U A D f‖ ≤ ‖f‖ := by
  have hn : (Fintype.card (D.G F ζ hζ hF U) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hg : ∀ g : D.G F ζ hζ hF U,
      ‖((((D.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) •
        Lp.compMeasurePreserving (D.orthogonal g)
          (chart_orthogonal_measurePreserving F ζ hζ hF U A D g) f)‖ = ‖f‖ := by
    intro g
    rw [norm_smul, Lp.norm_compMeasurePreserving]
    simp only [Units.val_inv_eq_inv_val, norm_inv,
      chart_rho_norm F ζ hζ hF U A D g, inv_one, one_mul]
  simp only [chartAverageBall, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  change ‖(Fintype.card (D.G F ζ hζ hF U) : ℂ)⁻¹ •
    ∑ g, (((D.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) •
      Lp.compMeasurePreserving (D.orthogonal g)
        (chart_orthogonal_measurePreserving F ζ hζ hF U A D g) f‖ ≤ ‖f‖
  rw [norm_smul]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
  simp only [hg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    norm_inv, Complex.norm_natCast]
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

 def chartRestrictBall (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (D : Chart F ζ hζ hF U A) :
    Lp ℂ 2 (volume.restrict (cube D.n D.a)) →L[ℂ]
      Lp ℂ 2 (volume.restrict (Metric.ball (0 : E D.n) D.radius)) := by
  let L : Lp ℂ 2 (volume.restrict (cube D.n D.a)) →ₗ[ℂ]
      Lp ℂ 2 (volume.restrict (Metric.ball (0 : E D.n) D.radius)) := {
    toFun f := ((Lp.memLp f).mono_measure (Measure.restrict_mono
      (Set.Subset.trans subset_closure
        (Set.Subset.trans D.closed_ball_in_cube interior_subset)) le_rfl)).toLp f
    map_add' f g := by
      apply Lp.ext
      grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
      exact ae_mono (Measure.restrict_mono (Set.Subset.trans subset_closure
        (Set.Subset.trans D.closed_ball_in_cube interior_subset)) le_rfl) (Lp.coeFn_add f g)
    map_smul' c f := by
      apply Lp.ext
      grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
      exact ae_mono (Measure.restrict_mono (Set.Subset.trans subset_closure
        (Set.Subset.trans D.closed_ball_in_cube interior_subset)) le_rfl) (Lp.coeFn_smul c f) }
  refine L.mkContinuous 1 ?_
  intro f
  simp only [one_mul]
  change ‖((Lp.memLp f).mono_measure (Measure.restrict_mono
      (Set.Subset.trans subset_closure
        (Set.Subset.trans D.closed_ball_in_cube interior_subset)) le_rfl)).toLp f‖ ≤ ‖f‖
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_measure _
      (Measure.restrict_mono (Set.Subset.trans subset_closure
        (Set.Subset.trans D.closed_ball_in_cube interior_subset)) le_rfl))

theorem bounded_character_averaging (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (D : Chart F ζ hζ hF U A) :
    ∃ Q : Lp ℂ 2 (volume.restrict (cube D.n D.a)) →L[ℂ]
        Lp ℂ 2 (volume.restrict (Metric.ball (0 : E D.n) D.radius)),
      (∀ f, Q f =ᵐ[volume.restrict (Metric.ball (0 : E D.n) D.radius)]
        D.average F ζ hζ hF U f) ∧ (∀ f, ‖Q f‖ ≤ ‖f‖) := by
  let Q := (chartAverageBall F ζ hζ hF U A D).comp (chartRestrictBall F ζ hζ hF U A D)
  refine ⟨Q, ?_, ?_⟩
  · intro f
    refine (chartAverageBall_formula F ζ hζ hF U A D _).trans ?_
    have ht := (show (chartRestrictBall F ζ hζ hF U A D f) =ᵐ[
      volume.restrict (Metric.ball (0 : E D.n) D.radius) ] f from MemLp.coeFn_toLp ((Lp.memLp f).mono_measure (Measure.restrict_mono
        (Set.Subset.trans subset_closure
          (Set.Subset.trans D.closed_ball_in_cube interior_subset)) le_rfl)))
    have hg := fun g : D.G F ζ hζ hF U =>
      (chart_orthogonal_measurePreserving F ζ hζ hF U A D g).quasiMeasurePreserving.ae_eq_comp ht
    filter_upwards [Filter.eventually_all.mpr hg] with x hx
    by_cases hxb : x ∈ Metric.ball (0 : E D.n) D.radius
    · simp only [Chart.average, Set.indicator_of_mem hxb]
      congr 1
      exact Finset.sum_congr rfl (fun g _ => congrArg (fun z : ℂ => (((D.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) * z) (hx g))
    · simp only [Chart.average, Set.indicator_of_notMem hxb]
  · intro f
    refine (chartAverageBall_bound F ζ hζ hF U A D _).trans ?_
    change ‖((Lp.memLp f).mono_measure (Measure.restrict_mono
      (Set.Subset.trans subset_closure
        (Set.Subset.trans D.closed_ball_in_cube interior_subset)) le_rfl)).toLp f‖ ≤ ‖f‖
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_measure _
      (Measure.restrict_mono (Set.Subset.trans subset_closure
        (Set.Subset.trans D.closed_ball_in_cube interior_subset)) le_rfl))

 theorem inversePhase_memLp (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (f : Lp ℂ 2 (volume.restrict (Metric.ball (0 : E (C.chart i).n)
      (C.chart i).radius))) :
    MemLp (fun x => (((P.phase i x)⁻¹ : ℂˣ) : ℂ) * f x) 2
      (volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)) := by
  have hm : AEStronglyMeasurable (fun x => (((P.phase i x)⁻¹ : ℂˣ) : ℂ))
      (volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)) := by
    simp only [Units.val_inv_eq_inv_val]
    exact (((comap_measurable _ : Measurable (Units.val : ℂˣ → ℂ)).comp
      (P.measurable_phase i)).inv).aestronglyMeasurable
  refine (Lp.memLp f).of_le (hm.mul (Lp.aestronglyMeasurable f)) ?_
  filter_upwards with x
  simp only [norm_mul, Units.val_inv_eq_inv_val, norm_inv, P.unitary_phase,
    inv_one, one_mul, le_refl]

 def inversePhaseLinear (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) :
    Lp ℂ 2 (volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)) →ₗ[ℂ]
      Lp ℂ 2 (volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)) where
  toFun f := (inversePhase_memLp F ζ hζ hF U A M C P i f).toLp _
  map_add' f g := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
    filter_upwards [Lp.coeFn_add f g] with x hx
    simp only [hx, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simp only [hx, Pi.smul_apply, smul_eq_mul, mul_left_comm, RingHom.id_apply]

 theorem inversePhaseLinear_norm (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (f : Lp ℂ 2 (volume.restrict (Metric.ball (0 : E (C.chart i).n)
      (C.chart i).radius))) :
    ‖inversePhaseLinear F ζ hζ hF U A M C P i f‖ = ‖f‖ := by
  change ‖(inversePhase_memLp F ζ hζ hF U A M C P i f).toLp _‖ = ‖f‖
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (inversePhase_memLp F ζ hζ hF U A M C P i f).coeFn_toLp]
  congr 1
  apply eLpNorm_congr_norm_ae
    (inversePhase_memLp F ζ hζ hF U A M C P i f).aestronglyMeasurable
    (Lp.aestronglyMeasurable f)
  filter_upwards with x
  simp only [norm_mul, Units.val_inv_eq_inv_val, norm_inv, P.unitary_phase,
    inv_one, one_mul]

 def inversePhaseMap (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) :
    Lp ℂ 2 (volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)) →L[ℂ]
      Lp ℂ 2 (volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)) :=
  (inversePhaseLinear F ζ hζ hF U A M C P i).mkContinuous 1 (fun f => by
    rw [one_mul, inversePhaseLinear_norm])

theorem bounded_untwisted_averaging (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) :
    ∃ S : Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a)) →L[ℂ]
        Lp ℂ 2 (volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)),
      (∀ f, S f =ᵐ[volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)]
        fun x => (((P.phase i x)⁻¹ : ℂˣ) : ℂ) *
          (C.chart i).average F ζ hζ hF U f x) ∧ (∀ f, ‖S f‖ ≤ ‖f‖) := by
  obtain ⟨Q, hQ, hQnorm⟩ := bounded_character_averaging F ζ hζ hF U A (C.chart i)
  refine ⟨(inversePhaseMap F ζ hζ hF U A M C P i).comp Q, ?_, ?_⟩
  · intro f
    refine (inversePhase_memLp F ζ hζ hF U A M C P i (Q f)).coeFn_toLp.trans ?_
    filter_upwards [hQ f] with x hx
    rw [hx]
  · intro f
    change ‖inversePhaseLinear F ζ hζ hF U A M C P i (Q f)‖ ≤ ‖f‖
    rw [inversePhaseLinear_norm]
    exact hQnorm f

theorem chart_average_equivariance (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (D : Chart F ζ hζ hF U A) (f : E D.n → ℂ)
    (h : D.G F ζ hζ hF U) (x : E D.n) :
    D.average F ζ hζ hF U f (D.orthogonal h x) =
      (D.rho F ζ hζ hF U h : ℂ) * D.average F ζ hζ hF U f x := by
  have hb : D.orthogonal h x ∈ Metric.ball (0 : E D.n) D.radius ↔
      x ∈ Metric.ball (0 : E D.n) D.radius := by
    simp only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
  by_cases hx : x ∈ Metric.ball (0 : E D.n) D.radius
  · simp only [Chart.average, Set.indicator_of_mem hx, Set.indicator_of_mem (hb.mpr hx)]
    rw [mul_left_comm]
    congr 1
    rw [Finset.mul_sum]
    apply Fintype.sum_equiv (Equiv.mulRight h)
    intro g
    have ho : D.orthogonal (g * h) x = D.orthogonal g (D.orthogonal h x) := by
      rw [map_mul]
      rfl
    change _ = (D.rho F ζ hζ hF U h : ℂ) *
      ((((D.rho F ζ hζ hF U (g * h))⁻¹ : ℂˣ) : ℂ) * f (D.orthogonal (g * h) x))
    rw [ho, map_mul, mul_inv_rev, Units.val_mul]
    have hc : (D.rho F ζ hζ hF U h : ℂ) *
        (((D.rho F ζ hζ hF U h)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]
      rfl
    rw [← mul_assoc, ← mul_assoc, hc, one_mul]
  · simp only [Chart.average, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (mt hb.mp hx), mul_zero]

theorem untwisted_average_invariant_ae (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (f : E (C.chart i).n → ℂ) (g : (C.chart i).G F ζ hζ hF U) :
    ∀ᵐ x ∂volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius),
      (((P.phase i ((C.chart i).orthogonal g x))⁻¹ : ℂˣ) : ℂ) *
        (C.chart i).average F ζ hζ hF U f ((C.chart i).orthogonal g x) =
      (((P.phase i x)⁻¹ : ℂˣ) : ℂ) * (C.chart i).average F ζ hζ hF U f x := by
  filter_upwards [P.phase_equivariance i g] with x hx
  rw [chart_average_equivariance]
  simp only [Units.val_inv_eq_inv_val]
  rw [hx, mul_inv_rev]
  have hc : ((C.chart i).rho F ζ hζ hF U g : ℂ)⁻¹ *
      ((C.chart i).rho F ζ hζ hF U g : ℂ) = 1 := by
    exact inv_mul_cancel₀ (Units.ne_zero _)
  rw [mul_assoc, ← mul_assoc ((↑((C.chart i).rho F ζ hζ hF U g) : ℂ)⁻¹), hc, one_mul]

theorem chartMeasure_le_volume (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (D : Chart F ζ hζ hF U A) :
    (Fintype.card (D.G F ζ hζ hF U) : ℝ≥0∞)⁻¹ •
      (volume.restrict (Metric.ball (0 : E D.n) D.radius)).withDensity
        (fun x => ENNReal.ofReal (D.weight x)) ≤
      ((Fintype.card (D.G F ζ hζ hF U) : ℝ≥0∞)⁻¹ * ENNReal.ofReal D.upper) •
        volume.restrict (Metric.ball (0 : E D.n) D.radius) := by
  have h : (volume.restrict (Metric.ball (0 : E D.n) D.radius)).withDensity
      (fun x => ENNReal.ofReal (D.weight x)) ≤
      ENNReal.ofReal D.upper • volume.restrict (Metric.ball (0 : E D.n) D.radius) := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact ENNReal.ofReal_le_ofReal (D.finite_bounds x (subset_closure hx)).2
  simpa only [smul_smul] using
    smul_le_smul_left ((Fintype.card (D.G F ζ hζ hF U) : ℝ≥0∞)⁻¹) h

theorem untwisted_average_memLp_weighted (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (f : Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a))) :
    MemLp (fun x => (((P.phase i x)⁻¹ : ℂˣ) : ℂ) *
      (C.chart i).average F ζ hζ hF U f x) 2
      ((Fintype.card ((C.chart i).G F ζ hζ hF U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)).withDensity
          (fun x => ENNReal.ofReal ((C.chart i).weight x))) := by
  obtain ⟨S, hS, _⟩ := bounded_untwisted_averaging F ζ hζ hF U A M C P i
  have hmem := (Lp.memLp (S f)).ae_eq (hS f)
  exact hmem.of_measure_le_smul
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by simp)) ENNReal.ofReal_ne_top)
    (chartMeasure_le_volume F ζ hζ hF U A (C.chart i))

theorem chart_quotient_secondCountable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) :
    SecondCountableTopology (X F ζ hζ U) := by
  letI (i : Fin A.componentCount) : SecondCountableTopology
      (KPCuspSiegel.OrbitQuotient F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))) :=
    (show IsOpenQuotientMap (KPCuspSiegel.projection F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))) from
      ⟨Quotient.mk_surjective, continuous_quot_mk,
        KPCuspSiegel.isOpenMap_projection F _⟩).secondCountableTopology
  exact A.components.symm.isEmbedding.secondCountableTopology

private theorem chart_toBase_continuous_ball (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (D : Chart F ζ hζ hF U A) :
    Continuous (Set.restrict (Metric.ball (0 : E D.n) D.radius)
      (D.toBase F ζ hζ hF U)) := by
  have hc : Continuous (fun z : KPFiniteCuspAtlas.SymmetricSpace F =>
      A.components ⟨D.component, KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative D.component)) z⟩) :=
    A.components.continuous.comp (continuous_sigmaMk.comp continuous_quot_mk)
  have hh := continuousOn_iff_continuous_restrict.mp
    (hc.comp_continuousOn (D.smooth_coordinates.continuousOn.mono
      (Set.Subset.trans subset_closure D.closed_ball_in_extension)))
  convert hh using 1
  funext x
  simp only [Set.restrict, Set.domRestrict_apply, Function.comp_apply, Chart.toBase]
  exact (A.components_formula D.component _).symm

theorem chart_measurable_descent (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (D : Chart F ζ hζ hF U A) (b : E D.n → ℂ) (hb : Measurable b)
    (hi : ∀ (g : D.G F ζ hζ hF U) x,
      x ∈ Metric.ball (0 : E D.n) D.radius → b (D.orthogonal g x) = b x) :
    ∃ f : X F ζ hζ U → ℂ, Measurable f ∧
      (∀ x ∈ Metric.ball (0 : E D.n) D.radius,
        f (D.toBase F ζ hζ hF U x) = b x) ∧
      (∀ x, x ∉ D.O F ζ hζ hF U → f x = 0) := by
  letI := quotient_hausdorff F ζ hζ hF U A
  letI := chart_quotient_secondCountable F ζ hζ hF U A
  letI : BorelSpace (X F ζ hζ U) := ⟨rfl⟩
  let B := Metric.ball (0 : E D.n) D.radius
  letI : PolishSpace B := Metric.isOpen_ball.polishSpace
  let O := D.O F ζ hζ hF U
  have hO : IsOpen O := by
    have h := CutoffConstruction.chart_ball_toBase_isOpenMap F ζ hζ hF U A D
      Set.univ isOpen_univ
    convert h using 1
    ext x
    change (∃ y ∈ B, D.toBase F ζ hζ hF U y = x) ↔
      (∃ y : B, y ∈ Set.univ ∧ D.toBase F ζ hζ hF U y.val = x)
    simp only [Set.mem_univ, true_and]
    exact ⟨fun ⟨y, hy, he⟩ => ⟨⟨y, hy⟩, he⟩,
      fun ⟨y, he⟩ => ⟨y.val, y.property, he⟩⟩
  let lift : O → E D.n := fun x => x.property.choose
  have hl : ∀ x : O, lift x ∈ B ∧ D.toBase F ζ hζ hF U (lift x) = x :=
    fun x => x.property.choose_spec
  let f : X F ζ hζ U → ℂ := fun x => if hx : x ∈ O then b (lift ⟨x, hx⟩) else 0
  have hf : ∀ x ∈ B, f (D.toBase F ζ hζ hF U x) = b x := by
    intro x hx
    have hpx : D.toBase F ζ hζ hF U x ∈ O := ⟨x, hx, rfl⟩
    rw [show f (D.toBase F ζ hζ hF U x) = b (lift ⟨_, hpx⟩) by simp [f, hpx]]
    obtain ⟨g, hg⟩ := (CutoffConstruction.chart_base_fibers F ζ hζ hF U A D
      (D.closed_ball_in_extension (subset_closure (hl ⟨_, hpx⟩).1))
      (D.closed_ball_in_extension (subset_closure hx))).mp (hl ⟨_, hpx⟩).2
    exact (hi g _ (hl ⟨_, hpx⟩).1).symm.trans (congrArg b hg)
  have hmeas : Measurable (Set.restrict O f) := by
    let p : B → O := fun x => ⟨D.toBase F ζ hζ hF U x, x.val, x.property, rfl⟩
    have hp : Measurable p := by
      exact Measurable.subtype_mk
        (chart_toBase_continuous_ball F ζ hζ hF U A D).measurable
    have hs : Function.Surjective p := by
      intro x
      refine ⟨⟨lift x, (hl x).1⟩, ?_⟩
      exact Subtype.ext (hl x).2
    apply (hp.measurable_comp_iff_of_surjective hs).mp
    have he : (Set.restrict O f) ∘ p = b ∘ Subtype.val := by
      funext x
      exact hf x x.property
    rw [he]
    exact hb.comp measurable_subtype_coe
  refine ⟨f, ?_, hf, ?_⟩
  · have hh := Measurable.dite hmeas (measurable_const (a := (0 : ℂ))) hO.measurableSet
    convert hh using 1
    funext x
    by_cases hx : x ∈ O <;> simp [Set.restrict, f, hx]
  · intro x hx
    have hxO : x ∉ O := hx
    simp [f, hxO]

theorem untwisted_average_measurable_invariant (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (f : Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a))) :
    ∃ b : E (C.chart i).n → ℂ, Measurable b ∧
      (∀ (g : (C.chart i).G F ζ hζ hF U) x, b ((C.chart i).orthogonal g x) = b x) ∧
      b =ᵐ[volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)]
        (fun x => (((P.phase i x)⁻¹ : ℂˣ) : ℂ) *
          (C.chart i).average F ζ hζ hF U f x) := by
  let D := C.chart i
  let μ := volume.restrict (Metric.ball (0 : E D.n) D.radius)
  let t : E D.n → ℂ := fun x => (((P.phase i x)⁻¹ : ℂˣ) : ℂ) * D.average F ζ hζ hF U f x
  obtain ⟨S, hS, _⟩ := bounded_untwisted_averaging F ζ hζ hF U A M C P i
  have hm : AEStronglyMeasurable t μ := ((Lp.memLp (S f)).ae_eq (hS f)).aestronglyMeasurable
  let m := hm.mk t
  let b : E D.n → ℂ := fun x => (Fintype.card (D.G F ζ hζ hF U) : ℂ)⁻¹ *
    ∑ g : D.G F ζ hζ hF U, m (D.orthogonal g x)
  have he : ∀ g : D.G F ζ hζ hF U, (fun x => m (D.orthogonal g x)) =ᵐ[μ] t := by
    intro g
    have hmk : (fun x => m (D.orthogonal g x)) =ᵐ[μ] (fun x => t (D.orthogonal g x)) :=
      (chart_orthogonal_measurePreserving F ζ hζ hF U A D g).quasiMeasurePreserving.ae_eq_comp
        (hm.ae_eq_mk.symm)
    exact hmk.trans (untwisted_average_invariant_ae F ζ hζ hF U A M C P i f g)
  refine ⟨b, ?_, ?_, ?_⟩
  · exact measurable_const.mul (Finset.measurable_sum _ (fun g _ =>
      hm.measurable_mk.comp (D.orthogonal g).continuous.measurable))
  · intro g x
    apply congrArg ((Fintype.card (D.G F ζ hζ hF U) : ℂ)⁻¹ * ·)
    apply Fintype.sum_bijective (fun h : D.G F ζ hζ hF U => h * g)
      (Group.mulRight_bijective g)
    intro h
    rw [map_mul]
    rfl
  · have hall : ∀ᵐ x ∂μ, ∀ g : D.G F ζ hζ hF U, m (D.orthogonal g x) = t x :=
      (ae_all_iff.mpr he)
    filter_upwards [hall] with x hx
    change (Fintype.card (D.G F ζ hζ hF U) : ℂ)⁻¹ * ∑ g, m (D.orthogonal g x) = t x
    rw [Finset.sum_congr rfl (fun g _ => hx g)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

theorem untwisted_average_measurable_descent (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (f : Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a))) :
    ∃ r : X F ζ hζ U → ℂ, Measurable r ∧
      (fun x => r ((C.chart i).toBase F ζ hζ hF U x)) =ᵐ[
        volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)]
        (fun x => (((P.phase i x)⁻¹ : ℂˣ) : ℂ) *
          (C.chart i).average F ζ hζ hF U f x) ∧
      (∀ x, x ∉ (C.chart i).O F ζ hζ hF U → r x = 0) := by
  obtain ⟨b, hb, hi, he⟩ := untwisted_average_measurable_invariant F ζ hζ hF U A M C P i f
  obtain ⟨r, hr, hf, hz⟩ := chart_measurable_descent F ζ hζ hF U A (C.chart i) b hb
    (fun g x _ => hi g x)
  refine ⟨r, hr, ?_, hz⟩
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet, he] with x hx hxe
  exact (hf x hx).trans hxe

private theorem chart_image_measurable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (D : Chart F ζ hζ hF U A) : MeasurableSet (D.O F ζ hζ hF U) := by
  letI : BorelSpace (X F ζ hζ U) := ⟨rfl⟩
  have h := CutoffConstruction.chart_ball_toBase_isOpenMap F ζ hζ hF U A D Set.univ isOpen_univ
  have he : Set.restrict (Metric.ball (0 : E D.n) D.radius) (D.toBase F ζ hζ hF U) '' Set.univ =
      D.O F ζ hζ hF U := by
    ext x
    simp only [Chart.O, Set.mem_image, Set.mem_univ, true_and]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  exact (he ▸ h).measurableSet

theorem untwisted_average_global_memLp (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (f : Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a)))
    (r : X F ζ hζ U → ℂ) (hr : Measurable r)
    (he : (fun x => r ((C.chart i).toBase F ζ hζ hF U x)) =ᵐ[
        volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)]
        (fun x => (((P.phase i x)⁻¹ : ℂˣ) : ℂ) * (C.chart i).average F ζ hζ hF U f x))
    (hz : ∀ x, x ∉ (C.chart i).O F ζ hζ hF U → r x = 0) :
    MemLp r 2 (quotientMeasure F ζ hζ hF U A) := by
  let D := C.chart i
  let ν := (Fintype.card (D.G F ζ hζ hF U) : ℝ≥0∞)⁻¹ •
    (volume.restrict (Metric.ball (0 : E D.n) D.radius)).withDensity
      (fun x => ENNReal.ofReal (D.weight x))
  have hac : ν ≪ volume.restrict (Metric.ball (0 : E D.n) D.radius) :=
    (withDensity_absolutelyContinuous _ _).smul_left _
  have hb : AEMeasurable (D.toBase F ζ hζ hF U) ν :=
    (chart_toBase_aemeasurable F ζ hζ hF U A D).mono_ac hac
  have hmem : MemLp (r ∘ D.toBase F ζ hζ hF U) 2 ν :=
    (untwisted_average_memLp_weighted F ζ hζ hF U A M C P i f).ae_eq (he.symm.filter_mono hac.ae_le)
  have hp : MemLp r 2 ((quotientMeasure F ζ hζ hF U A).restrict (D.O F ζ hζ hF U)) := by
    rw [← C.chart_measure i]
    exact (memLp_map_measure_iff hr.aestronglyMeasurable hb).mpr hmem
  have hs : (D.O F ζ hζ hF U).indicator r = r :=
    Set.indicator_eq_self.mpr (by intro x hx; by_contra hn; exact hx (hz x hn))
  rw [← hs]
  exact (memLp_indicator_iff_restrict (chart_image_measurable F ζ hζ hF U A D).nullMeasurableSet).mpr hp

 theorem chart_descent_ae_unique (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    {K : Set (X F ζ hζ U)} (C : FiniteCutoffs F ζ hζ hF U A K) (i : Fin C.count)
    {r s : X F ζ hζ U → ℂ} (hr : Measurable r) (hs : Measurable s)
    (he : (r ∘ (C.chart i).toBase F ζ hζ hF U) =ᵐ[
      volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)]
      (s ∘ (C.chart i).toBase F ζ hζ hF U))
    (hzr : ∀ x, x ∉ (C.chart i).O F ζ hζ hF U → r x = 0)
    (hzs : ∀ x, x ∉ (C.chart i).O F ζ hζ hF U → s x = 0) :
    r =ᵐ[quotientMeasure F ζ hζ hF U A] s := by
  let D := C.chart i
  let ν := (Fintype.card (D.G F ζ hζ hF U) : ℝ≥0∞)⁻¹ •
    (volume.restrict (Metric.ball (0 : E D.n) D.radius)).withDensity
      (fun x => ENNReal.ofReal (D.weight x))
  have hac : ν ≪ volume.restrict (Metric.ball (0 : E D.n) D.radius) :=
    (withDensity_absolutelyContinuous _ _).smul_left _
  have hb : AEMeasurable (D.toBase F ζ hζ hF U) ν :=
    (chart_toBase_aemeasurable F ζ hζ hF U A D).mono_ac hac
  have hp : r =ᵐ[(quotientMeasure F ζ hζ hF U A).restrict (D.O F ζ hζ hF U)] s := by
    rw [← C.chart_measure i]
    exact (ae_map_iff hb (measurableSet_eq_fun hr hs)).mpr (he.filter_mono hac.ae_le)
  have hh := (ae_restrict_iff' (chart_image_measurable F ζ hζ hF U A D)).mp hp
  filter_upwards [hh] with x hx
  by_cases hxO : x ∈ D.O F ζ hζ hF U
  · exact hx hxO
  · rw [hzr x hxO, hzs x hxO]

 def scalarDescent (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (f : Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a))) :
    X F ζ hζ U → ℂ :=
  (untwisted_average_measurable_descent F ζ hζ hF U A M C P i f).choose

 theorem scalarDescent_spec (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (f : Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a))) :
    Measurable (scalarDescent F ζ hζ hF U A M C P i f) ∧
    (fun x => scalarDescent F ζ hζ hF U A M C P i f ((C.chart i).toBase F ζ hζ hF U x)) =ᵐ[
      volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)]
      (fun x => (((P.phase i x)⁻¹ : ℂˣ) : ℂ) * (C.chart i).average F ζ hζ hF U f x) ∧
    (∀ x, x ∉ (C.chart i).O F ζ hζ hF U → scalarDescent F ζ hζ hF U A M C P i f x = 0) :=
  (untwisted_average_measurable_descent F ζ hζ hF U A M C P i f).choose_spec

 theorem scalarDescent_memLp (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (f : Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a))) :
    MemLp (scalarDescent F ζ hζ hF U A M C P i f) 2 (quotientMeasure F ζ hζ hF U A) := by
  have h := scalarDescent_spec F ζ hζ hF U A M C P i f
  exact untwisted_average_global_memLp F ζ hζ hF U A M C P i f _ h.1 h.2.1 h.2.2

 theorem scalarDescent_comp_S (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count)
    (S : Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a)) →L[ℂ]
      Lp ℂ 2 (volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)))
    (hS : ∀ f, S f =ᵐ[volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)]
      (fun x => (((P.phase i x)⁻¹ : ℂˣ) : ℂ) * (C.chart i).average F ζ hζ hF U f x))
    (f : Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a))) :
    (scalarDescent F ζ hζ hF U A M C P i f ∘ (C.chart i).toBase F ζ hζ hF U) =ᵐ[
      volume.restrict (Metric.ball (0 : E (C.chart i).n) (C.chart i).radius)] S f :=
  (scalarDescent_spec F ζ hζ hF U A M C P i f).2.1.trans (hS f).symm

 def scalarDescentLinear (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) : Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a)) →ₗ[ℂ]
      Lp ℂ 2 (quotientMeasure F ζ hζ hF U A) where
  toFun f := (scalarDescent_memLp F ζ hζ hF U A M C P i f).toLp _
  map_add' f g := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
    obtain ⟨S, hS, _⟩ := bounded_untwisted_averaging F ζ hζ hF U A M C P i
    have hc := scalarDescent_comp_S F ζ hζ hF U A M C P i S hS
    have hr := scalarDescent_spec F ζ hζ hF U A M C P i
    apply chart_descent_ae_unique F ζ hζ hF U A C i (hr (f + g)).1 ((hr f).1.add (hr g).1)
    · filter_upwards [hc (f + g), hc f, hc g, Lp.coeFn_add (S f) (S g)] with x hfg hf hg hh
      simp only [Function.comp_apply, Pi.add_apply] at *
      rw [hfg, hf, hg, map_add, hh]
    · exact (hr (f + g)).2.2
    · intro x hx
      simp [(hr f).2.2 x hx, (hr g).2.2 x hx]
  map_smul' c f := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
    obtain ⟨S, hS, _⟩ := bounded_untwisted_averaging F ζ hζ hF U A M C P i
    have hc := scalarDescent_comp_S F ζ hζ hF U A M C P i S hS
    have hr := scalarDescent_spec F ζ hζ hF U A M C P i
    apply chart_descent_ae_unique F ζ hζ hF U A C i (hr (c • f)).1 ((hr f).1.const_smul c)
    · filter_upwards [hc (c • f), hc f, Lp.coeFn_smul c (S f)] with x hcf hf hh
      simp only [Function.comp_apply, Pi.smul_apply, RingHom.id_apply] at *
      rw [hcf, hf, map_smul, hh]
    · exact (hr (c • f)).2.2
    · intro x hx
      simp [(hr f).2.2 x hx]

 theorem scalarDescentLinear_bound (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (f : Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a))) :
    ‖scalarDescentLinear F ζ hζ hF U A M C P i f‖ ≤
      (((Fintype.card ((C.chart i).G F ζ hζ hF U) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (C.chart i).upper) ^ (1 / (2 : ℝ≥0∞)).toReal).toReal * ‖f‖ := by
  let D := C.chart i
  let r := scalarDescent F ζ hζ hF U A M C P i f
  let ν := (Fintype.card (D.G F ζ hζ hF U) : ℝ≥0∞)⁻¹ •
    (volume.restrict (Metric.ball (0 : E D.n) D.radius)).withDensity
      (fun x => ENNReal.ofReal (D.weight x))
  let c := (Fintype.card (D.G F ζ hζ hF U) : ℝ≥0∞)⁻¹ * ENNReal.ofReal D.upper
  have hc : c ≠ ∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by simp)) ENNReal.ofReal_ne_top
  have hac : ν ≪ volume.restrict (Metric.ball (0 : E D.n) D.radius) :=
    (withDensity_absolutelyContinuous _ _).smul_left _
  have hb : AEMeasurable (D.toBase F ζ hζ hF U) ν :=
    (chart_toBase_aemeasurable F ζ hζ hF U A D).mono_ac hac
  obtain ⟨S, hS, hSnorm⟩ := bounded_untwisted_averaging F ζ hζ hF U A M C P i
  have he : eLpNorm r 2 (quotientMeasure F ζ hζ hF U A) = eLpNorm (S f) 2 ν := by
    have hr := scalarDescent_spec F ζ hζ hF U A M C P i f
    have hind : (D.O F ζ hζ hF U).indicator r = r := Set.indicator_eq_self.mpr
      (by intro x hx; by_contra hn; exact hx (hr.2.2 x hn))
    calc
      eLpNorm r 2 (quotientMeasure F ζ hζ hF U A) =
          eLpNorm r 2 ((quotientMeasure F ζ hζ hF U A).restrict (D.O F ζ hζ hF U)) := by
        conv_lhs => rw [← hind]
        rw [eLpNorm_indicator_eq_eLpNorm_restrict (chart_image_measurable F ζ hζ hF U A D).nullMeasurableSet]
      _ = eLpNorm (r ∘ D.toBase F ζ hζ hF U) 2 ν := by
        rw [← C.chart_measure i]
        exact eLpNorm_map_measure hr.1.aestronglyMeasurable hb
      _ = eLpNorm (S f) 2 ν := eLpNorm_congr_ae
        ((scalarDescent_comp_S F ζ hζ hF U A M C P i S hS f).filter_mono hac.ae_le)
  have hle : eLpNorm r 2 (quotientMeasure F ζ hζ hF U A) ≤
      c ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm (S f) 2
        (volume.restrict (Metric.ball (0 : E D.n) D.radius)) := by
    rw [he]
    exact (eLpNorm_mono_measure _ (chartMeasure_le_volume F ζ hζ hF U A D)).trans
      (eLpNorm_smul_measure_le c _ _ _)
  have hfin : c ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm (S f) 2
      (volume.restrict (Metric.ball (0 : E D.n) D.radius)) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hc) (Lp.eLpNorm_ne_top _)
  change ‖(scalarDescent_memLp F ζ hζ hF U A M C P i f).toLp _‖ ≤ _
  rw [Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  exact (ENNReal.toReal_mono hfin hle).trans (by
    rw [ENNReal.toReal_mul]
    exact mul_le_mul_of_nonneg_left (hSnorm f) ENNReal.toReal_nonneg)

 def scalarDescentMap (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) : Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a)) →L[ℂ]
      Lp ℂ 2 (quotientMeasure F ζ hζ hF U A) :=
  (scalarDescentLinear F ζ hζ hF U A M C P i).mkContinuous _
    (scalarDescentLinear_bound F ζ hζ hF U A M C P i)

 def restrictGlobalMap (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (K : Set (X F ζ hζ U)) : H F ζ hζ hF U A →L[ℂ] HK F ζ hζ hF U A K := by
  let L : H F ζ hζ hF U A →ₗ[ℂ] HK F ζ hζ hF U A K := {
    toFun v := ((Lp.memLp v).restrict K).toLp v
    map_add' v w := by
      apply Lp.ext
      grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
      exact ae_mono Measure.restrict_le_self (Lp.coeFn_add v w)
    map_smul' c v := by
      apply Lp.ext
      grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
      exact ae_mono Measure.restrict_le_self (Lp.coeFn_smul c v) }
  refine LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := H F ζ hζ hF U A) (F := HK F ζ hζ hF U A K) L 1 ?_
  intro v
  change ‖((Lp.memLp v).restrict K).toLp v‖ ≤ 1 * ‖v‖
  rw [one_mul, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_mono_measure _ Measure.restrict_le_self)

 def descentMap (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) : Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a)) →L[ℂ]
      HK F ζ hζ hF U A K :=
  (restrictGlobalMap F ζ hζ hF U A K).comp
    (((V F ζ hζ U).orthogonalProjectionOnto.compLpL 2 (quotientMeasure F ζ hζ hF U A)).comp
      (scalarDescentMap F ζ hζ hF U A M C P i))

private theorem descentMap_formula_global (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (P : FrameComparison F ζ hζ hF U A M C)
    (i : Fin C.count) (f : Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a))) :
    descentMap F ζ hζ hF U A M C P i f =ᵐ[(quotientMeasure F ζ hζ hF U A).restrict K]
      (fun x => (V F ζ hζ U).orthogonalProjectionOnto
        (scalarDescent F ζ hζ hF U A M C P i f x)) := by
  have hp := (V F ζ hζ U).orthogonalProjectionOnto.coeFn_compLpL
    (scalarDescentMap F ζ hζ hF U A M C P i f)
  have hs : scalarDescentMap F ζ hζ hF U A M C P i f =ᵐ[quotientMeasure F ζ hζ hF U A]
      scalarDescent F ζ hζ hF U A M C P i f :=
    MemLp.coeFn_toLp (scalarDescent_memLp F ζ hζ hF U A M C P i f)
  have hres : descentMap F ζ hζ hF U A M C P i f =ᵐ[
      (quotientMeasure F ζ hζ hF U A).restrict K]
      ((V F ζ hζ U).orthogonalProjectionOnto.compLpL 2 (quotientMeasure F ζ hζ hF U A)
        (scalarDescentMap F ζ hζ hF U A M C P i f)) := by
    exact MemLp.coeFn_toLp ((Lp.memLp
      ((V F ζ hζ U).orthogonalProjectionOnto.compLpL 2 (quotientMeasure F ζ hζ hF U A)
        (scalarDescentMap F ζ hζ hF U A M C P i f))).restrict K)
  filter_upwards [hres, ae_mono Measure.restrict_le_self hp, ae_mono Measure.restrict_le_self hs]
    with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]

private theorem bounded_local_operators_rank_one
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (hK : MeasurableSet K) (C : FiniteCutoffs F ζ hζ hF U A K)
    (P : FrameComparison F ζ hζ hF U A M C) (hV : V F ζ hζ U = ⊤) :
    Nonempty (LocalOperators F ζ hζ hF U A M C P) := by
  obtain ⟨T, hT, hTsmooth⟩ := bounded_cutoff_lifting F ζ hζ hF U A M C P

  have hR : ∃ R : ∀ i,
      Lp ℂ 2 (volume.restrict (cube (C.chart i).n (C.chart i).a)) →L[ℂ]
        HK F ζ hζ hF U A K,
      (∀ i f, ∀ᵐ x ∂volume.restrict (Metric.ball 0 (C.chart i).radius),
        (C.chart i).toBase F ζ hζ hF U x ∈ K →
        R i f ((C.chart i).toBase F ζ hζ hF U x) =
          (V F ζ hζ U).orthogonalProjectionOnto
            (((P.phase i x)⁻¹ : ℂˣ) * (C.chart i).average F ζ hζ hF U f x)) ∧
      (∀ i f, ∀ᵐ x ∂(quotientMeasure F ζ hζ hF U A).restrict K,
        x ∉ (C.chart i).O F ζ hζ hF U → R i f x = 0) := by
    refine ⟨descentMap F ζ hζ hF U A M C P, ?_, ?_⟩
    · intro i f
      have hg := (ae_restrict_iff' hK).mp
        (descentMap_formula_global F ζ hζ hF U A M C P i f)
      have hp := chartMeasure_pullback_ae F ζ hζ hF U A C i hg
      have hs := (scalarDescent_spec F ζ hζ hF U A M C P i f).2.1
      filter_upwards [hp, hs] with x hx hsx
      intro hxK
      rw [hx hxK, hsx]
    · intro i f
      filter_upwards [descentMap_formula_global F ζ hζ hF U A M C P i f] with x hx
      intro hxO
      rw [hx, (scalarDescent_spec F ζ hζ hF U A M C P i f).2.2 x hxO, map_zero]
  obtain ⟨R, hRformula, hRzero⟩ := hR
  exact ⟨⟨T, hT, R, hRformula, hRzero, hTsmooth⟩⟩

theorem bounded_local_operators (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (hK : MeasurableSet K) (C : FiniteCutoffs F ζ hζ hF U A K)
    (P : FrameComparison F ζ hζ hF U A M C) :
    Nonempty (LocalOperators F ζ hζ hF U A M C P) := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (V F ζ hζ U) with hV | hV
  · exact bounded_local_operators_rank_zero F ζ hζ hF U A M hK C P hV
  · exact bounded_local_operators_rank_one F ζ hζ hF U A M hK C P hV

end DedekindZetaZeroFree.CoreChartLocalizers

end
