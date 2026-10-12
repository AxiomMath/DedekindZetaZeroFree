module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.WeakSections.SupportAndMultiplication
public import DedekindZetaZeroFree.Analysis.EllipticRegularity.LocalH1EnergyEstimates

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory Topology
set_option maxHeartbeats 1500000
namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
attribute [local instance 2000] KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualCotangentMeasurableFamilies KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContActualCotangentChartRestriction
open KPContActualSectorChartEquivariantInputs KPContSectorLineL2Isometry
open KPContLocalNorm KPContSectorSmoothFramesSupport
open KPContActualCotangentCountableShrinking KPContCotangentActualGenuineTwistIsotropy
open KPContSectorPhaseComponentCharts
open KPContActualSectorCoordinateNullEquivalence KPContActualSectorFormWeakLocalization
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private lemma d_pos (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : 0 < d F := by
  have h := KPArch.complex_places_of_primitive_twelfth_root F ζ hζ
  rw [show d F = Module.finrank ℚ F / 2 from rfl, ← h.2.1]
  exact h.2.2

private lemma exists_ball_exhaustion (n : ℕ) (hn : 0 < n) (U : Set (Space n))
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ B : ℕ → LocalBall n,
      (∀ k, IsCompact (closure (B k).carrier)) ∧
      (∀ k, closure (B k).carrier ⊆ U) ∧
      U = ⋃ k, (B k).carrier := by
  classical
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense (Space n)
  set Q : Set (Space n × ℚ) :=
    {p | p.1 ∈ s ∧ 0 < p.2 ∧ Metric.closedBall p.1 (p.2 : ℝ) ⊆ U} with hQ
  have hQc : Q.Countable := by
    refine (hsc.prod (Set.countable_univ)).mono ?_
    rintro ⟨q, r⟩ ⟨h1, h2, _⟩
    exact ⟨h1, trivial⟩
  set P : Set (Space n × ℝ) := (fun p : Space n × ℚ => (p.1, (p.2 : ℝ))) '' Q with hP
  have hPc : P.Countable := hQc.image _
  have key : ∀ x ∈ U, ∃ p ∈ P, x ∈ Metric.ball p.1 p.2 ∧ Metric.closedBall p.1 p.2 ⊆ U := by
    intro x hx
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
    have hcU : Metric.closedBall x (ε/2) ⊆ U :=
      (Metric.closedBall_subset_ball (by linarith)).trans hεU
    have hxcl : x ∈ closure s := by rw [hsd.closure_eq]; exact Set.mem_univ x
    obtain ⟨q, hqs, hqx⟩ := Metric.mem_closure_iff.mp hxcl (ε/8) (by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show (ε/8:ℝ) < ε/4 by linarith)
    have hrpos : (0:ℚ) < r := by
      have h0 : (0:ℝ) < (r:ℝ) := lt_trans (by linarith : (0:ℝ) < ε/8) hr1
      exact_mod_cast h0
    have hq' : dist q x < ε/8 := by simpa [dist_comm] using hqx
    have hcl : Metric.closedBall q (r:ℝ) ⊆ U := by
      refine (Metric.closedBall_subset_closedBall' ?_).trans hcU
      have hr2' : (r:ℝ) < ε/4 := hr2
      linarith
    refine ⟨(q, (r:ℝ)), ?_, ?_, hcl⟩
    · exact ⟨⟨q, r⟩, ⟨hqs, hrpos, hcl⟩, rfl⟩
    · rw [Metric.mem_ball]
      have hr1' : (ε/8:ℝ) < (r:ℝ) := hr1
      linarith
  have hPne : P.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨p, hp, -⟩ := key x hx
    exact ⟨p, hp⟩
  obtain ⟨f, hf⟩ := hPc.exists_eq_range hPne
  have hfP : ∀ k, f k ∈ P := fun k => hf ▸ Set.mem_range_self k
  have hpos : ∀ k, 0 < (f k).2 := by
    intro k
    obtain ⟨⟨q, r⟩, ⟨-, hr, -⟩, heq⟩ := hfP k
    have h2 : (f k).2 = (r:ℝ) := by rw [← heq]
    rw [h2]
    have : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
    exact this
  let B : ℕ → LocalBall n := fun k => ⟨hn, (f k).1, (f k).2, hpos k⟩
  have hB : ∀ k, (B k).carrier = Metric.ball (f k).1 (f k).2 := fun k => rfl
  have hclP : ∀ k, Metric.closedBall (f k).1 (f k).2 ⊆ U := by
    intro k
    obtain ⟨⟨q, r⟩, ⟨-, -, hrU⟩, heq⟩ := hfP k
    have h1 : (f k).1 = q := by rw [← heq]
    have h2 : (f k).2 = (r:ℝ) := by rw [← heq]
    rw [h1, h2]; exact hrU
  refine ⟨B, ?_, ?_, ?_⟩
  · intro k
    rw [hB k]
    exact (isCompact_closedBall (f k).1 (f k).2).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  · intro k
    rw [hB k]
    exact Metric.closure_ball_subset_closedBall.trans (hclP k)
  · ext x
    constructor
    · intro hx
      obtain ⟨p, hpP, hxb, hcl⟩ := key x hx
      obtain ⟨k, hk⟩ := Set.mem_range.mp (hf ▸ hpP)
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      rw [hB k, hk]
      exact hxb
    · intro hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      rw [hB k] at hk
      exact hclP k (Metric.closure_ball_subset_closedBall (subset_closure hk))

private lemma continuous_toActual : Continuous (toActual (F := F) (ζ := ζ) (hζ := hζ)) := by
  unfold toActual labeledA
  fun_prop

private lemma isOpen_chart (a : ActualChart (U := U) (H := H)) : IsOpen (chart a) := a.domain_open.preimage continuous_toActual
private lemma toActual_fromActual (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
    toActual (ζ := ζ) (hζ := hζ) (fromActual (ζ := ζ) (hζ := hζ) y) = y := by
  simp only [toActual, fromActual, LinearIsometryEquiv.symm_apply_apply]
  funext k
  simp [labeledA, labeledAInv]
private theorem sectionFields_apply_actual (s : Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    sectionFields s a x = (s a.component).val (labeledA (placeEquiv F ζ hζ) x.val) := by
  have hcoe : (isotropyChart a).coefficient s x.val =
      (KPCuspGenuineMonodromy.chi F ζ hζ ((isotropyChart a).splitting x.val) : ℂ) *
        (s a.component).val
          ((isotropyChart a).kind.representative • labeledA (isotropyChart a).places x.val) := rfl
  rw [sectionFields, hcoe]
  simp [isotropyChart, KPContCotangentActualOverlap.ChartKind.representative]
private lemma scalar_eq_on_chart (s : BorelL2Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : Space (3 * d F)) (hx : x ∈ chart a) :
    scalar s a x = (s.val a.component).val (toActual (ζ := ζ) (hζ := hζ) x) := by
  have hx' : (baseReindex (F := F)).symm x ∈ omega a := hx
  unfold scalar liftExtension
  rw [dif_pos hx', sectionFields_apply_actual]
  rfl
 def baseFlat (a : ActualChart (U := U) (H := H)) (x : Space (3 * d F)) :=
  (H.atlas U).components ⟨a.component, Quotient.mk _ (toActual (ζ := ζ) (hζ := hζ) x)⟩
private theorem baseFlat_continuous (a : ActualChart (U := U) (H := H)) : Continuous (baseFlat a) := by
  have he : baseFlat a = KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component) ∘
    KPCuspSiegel.projection F (Component F ζ hζ U R P H a.component) ∘ toActual (ζ := ζ) (hζ := hζ) := by
    funext x; exact (H.atlas U).components_formula a.component _
  rw [he]
  have hc : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)) := by
    have he : KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component) =
        (H.atlas U).components ∘ Sigma.mk a.component := by
      funext p; exact ((H.atlas U).components_formula a.component p).symm
    rw [he]; exact (H.atlas U).components.continuous.comp continuous_sigmaMk
  exact hc.comp (continuous_quotient_mk'.comp continuous_toActual)
private theorem baseFlat_measurable (a : ActualChart (U := U) (H := H)) : Measurable (baseFlat a) := (baseFlat_continuous a).measurable
private theorem baseFlat_lift (a : ActualChart (U := U) (H := H)) (y : a.domain) :
    baseFlat a (fromActual (ζ := ζ) (hζ := hζ) y.val) = a.toBase y := by
  unfold baseFlat
  rw [toActual_fromActual]
  exact (H.atlas U).components_formula a.component _
private theorem normFlat (s : BorelL2Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : Space (3 * d F)) (hx : x ∈ chart a) :
    squaredNorm F ζ hζ U R P H s.val (baseFlat a x) = ENNReal.ofReal (‖scalar s a x‖ ^ 2) := by
  unfold squaredNorm baseFlat
  rw [sectionNorm_component, scalar_eq_on_chart s a x hx]
private theorem coefficientFlat (W : Family (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (x : Space (3 * d F)) (hx : x ∈ chart a) :
    normSquare W (baseFlat a x) = ‖liftExtension a (coefficient W a) ((baseReindex (F := F)).symm x)‖₊ ^ 2 := by
  have hx' : (baseReindex (F := F)).symm x ∈ omega a := hx
  have hq : baseFlat a x = q a ((baseReindex (F := F)).symm x) := by
    unfold baseFlat KPContCotangentOverlapRationalBranches.q
    exact (H.atlas U).components_formula a.component _
  rw [hq, normSquare_chart W a ⟨_, hx'⟩]
  simp only [liftExtension, dif_pos hx']
private theorem decode_zero (W : Family (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (x : Space (3 * d F)) (h : ∀ j, coordinateW W a x j = 0) :
    liftExtension a (coefficient W a) ((baseReindex (F := F)).symm x) = 0 := by
  apply PiLp.ext
  rintro ⟨i,k⟩
  have hk := h (coefficientIndex (F := F) (i, ![2, 0, 1] k))
  simp only [coordinateW, Equiv.symm_apply_apply] at hk
  fin_cases k <;> simp_all [Real.exp_ne_zero]
private theorem lp_locallyIntegrable {n : ℕ} (B : LocalBall n) (u : BallL2 B) :
    LocallyIntegrableOn u B.carrier (volume.restrict B.carrier) := by
  apply (locallyIntegrableOn_iff (μ := volume.restrict B.carrier)
    (f := (fun x => u x)) (s := B.carrier) B.toOpens.isOpen.isLocallyClosed).2
  intro K hK hKc
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hKc.measure_ne_top
  change Integrable _ ((volume.restrict B.carrier).restrict K)
  rw [Measure.restrict_restrict hKc.measurableSet, Set.inter_eq_left.mpr hK]
  exact ((Lp.memLp u).mono_measure (Measure.restrict_mono hK le_rfl)).integrable (by norm_num)
private theorem weakDerivative_zero {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (u d : BallL2 B) (hu : u =ᵐ[volume.restrict B.carrier] (fun _ => 0))
    (hd : IsWeakDerivative B α u d) : ∀ᵐ x ∂volume.restrict B.carrier, d x = 0 := by
  have hi := lp_locallyIntegrable B d
  have hz : ∀ᵐ x ∂volume.restrict B.carrier, x ∈ B.carrier → d x = 0 := by
    apply B.toOpens.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hi
    intro φ hφ hφc hφs
    have hcast : ContDiff ℝ (⊤ : ℕ∞) (fun x => (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
    have hsupp : tsupport (fun x => (φ x : ℂ)) = tsupport φ := by
      unfold tsupport; congr 1; ext x; simp
    let ψ : TestFunction B.toOpens ℂ ⊤ := ⟨fun x => (φ x : ℂ), hcast,
      by change IsCompact _; rw [hsupp]; exact hφc, hsupp ▸ hφs⟩
    have he : ∫ x in B.carrier, d x * ψ x = 0 := by
      apply mul_left_cancel₀ (pow_ne_zero α.degree (by norm_num : (-1 : ℂ) ≠ 0))
      rw [mul_zero, ← hd ψ]
      have h0 : (fun x => u x * coordinateDerivative α (fun y => ψ y) x) =ᵐ[volume.restrict B.carrier] (fun _ => 0) := by
        filter_upwards [hu] with x hx; rw [hx, zero_mul]
      rw [integral_congr_ae h0, integral_zero]
    simpa only [show (fun x => ψ x) = (fun x => (φ x : ℂ)) from rfl, Complex.real_smul, mul_comm] using he
  filter_upwards [hz, ae_restrict_mem B.toOpens.isOpen.measurableSet] with x hx hxB
  exact hx hxB

theorem weakChartData_zero_on_ball (s : BorelL2Sections F ζ hζ U R P H)
    (W : Family (U := U) (H := H)) (hs : WeakChartData s W)
    (a : ActualChart (U := U) (H := H)) (B : LocalBall (3*d F)) (hB : InteriorBall a B)
    (hzero : scalarCoordinate s a =ᵐ[volume.restrict B.carrier] (fun _ => 0)) :
    ∀ j, (fun x => covariantCoordinate W a x j) =ᵐ[volume.restrict B.carrier] (fun _ => 0) := by
  obtain ⟨h,hv,hg⟩ := hs a B hB 1
  have hchi : (KPCuspGenuineMonodromy.chi F ζ hζ (1 : rootsOfUnity 3 F) : ℂ) = 1 := by simp
  simp only [hchi, one_mul] at hv hg
  intro j
  have hz : h.derivatives (zeroIndex (3*d F)) =ᵐ[volume.restrict B.carrier] (fun _ => 0) := hv.trans hzero
  have hidx : ((KPContLocalEnergy.firstIndex j).val j).val = 1 := by simp [KPContLocalEnergy.firstIndex]
  exact (hg _ j hidx).symm.trans (weakDerivative_zero B _ _ _ hz (h.weak_derivatives _))

theorem zero_off_closed_of_balls (s : BorelL2Sections F ζ hζ U R P H)
    (W : Family (U := U) (H := H)) (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsClosed K)
    (hs : ∀ᵐ b ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P,
      b ∉ K → squaredNorm F ζ hζ U R P H s.val b = 0)
    (hlocal : ∀ (a : ActualChart (U := U) (H := H)) (B : LocalBall (3*d F)),
      InteriorBall a B → (scalar s a =ᵐ[volume.restrict B.carrier] (fun _ => 0)) →
        ∀ j, (fun x => coordinateW W a x j) =ᵐ[volume.restrict B.carrier] (fun _ => 0)) :
    ∀ᵐ b ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P, b ∉ K → normSquare W b = 0 := by
  let cover := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  let G := fun b => b ∉ K → normSquare W b = 0
  have hG : MeasurableSet {b | G b} := by
    have hm := hK.measurableSet.union (measurableSet_eq_fun (measurable_normSquare W) (measurable_const (a := (0 : ℝ≥0))))
    convert hm using 1; ext b; simp [G]; tauto
  have hchart : ∀ n, ∀ᵐ b ∂(KPContActualSectorCotangentL2.muU F ζ hζ U R P).restrict (cover.chart n).baseDomain, G b := by
    intro n
    let a := cover.chart n
    have hp := every_shrunkChart_properties F ζ hζ U R P H a
    have hsLift : ∀ᵐ y ∂a.liftedMeasure, a.toBase y ∉ K → squaredNorm F ζ hζ U R P H s.val (a.toBase y) = 0 := by
      have hm : MeasurableSet {b | b ∉ K → squaredNorm F ζ hζ U R P H s.val b = 0} := by
        have ht := hK.measurableSet.union (measurableSet_eq_fun (squaredNorm_measurable F ζ hζ U R P H s.val s.property.1)
          (measurable_const (a := (0 : ℝ≥0∞))))
        convert ht using 1; ext b; simp; tauto
      apply (ae_map_iff hp.measurable.aemeasurable hm).mp
      rw [hp.exact_pushforward]
      exact hs.filter_mono (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le
    have hΦ : Measurable (fun y : a.domain => fromActual (ζ := ζ) (hζ := hζ) y.val) := by
      have hc : Continuous (fun y : a.domain => fromActual (ζ := ζ) (hζ := hζ) y.val) := by
        unfold fromActual labeledAInv
        exact (baseReindex (F:=F)).continuous.comp ((CotangentLogCoframe.A (d F)).symm.continuous.comp
          (continuous_pi fun k => (continuous_apply _).comp continuous_subtype_val))
      exact hc.measurable
    have hsFlat : ∀ᵐ x ∂volume.restrict (chart a), baseFlat a x ∉ K → scalar s a x = 0 := by
      have hmeas : MeasurableSet {x | baseFlat a x ∉ K → squaredNorm F ζ hζ U R P H s.val (baseFlat a x) = 0} := by
        have ht := ((baseFlat_measurable a) hK.measurableSet).union
          (measurableSet_eq_fun ((squaredNorm_measurable F ζ hζ U R P H s.val s.property.1).comp (baseFlat_measurable a))
            (measurable_const (a := (0 : ℝ≥0∞))))
        convert ht using 1; ext x; simp; tauto
      have hw : ∀ᵐ x ∂KPChartL2.weightedMeasure (3*d F) (chart a) (weight a),
          baseFlat a x ∉ K → squaredNorm F ζ hζ U R P H s.val (baseFlat a x) = 0 := by
        rw [← lifted_measure_transport (a := a)]
        apply (ae_map_iff hΦ.aemeasurable hmeas).mpr
        simpa only [baseFlat_lift] using hsLift
      rw [KPChartL2.weightedMeasure] at hw
      change ∀ᵐ x ∂(volume.restrict (scalarData a).chart).withDensity (ENNReal.ofReal ∘ (scalarData a).weight),
        baseFlat a x ∉ K → squaredNorm F ζ hζ U R P H s.val (baseFlat a x) = 0 at hw
      have hac := withDensity_absolutelyContinuous' (μ := volume.restrict (chart a))
        (ENNReal.measurable_ofReal.comp_aemeasurable ((scalarData a).smooth_weight.continuousOn.aemeasurable (isOpen_chart a).measurableSet))
        (by filter_upwards [ae_restrict_mem (isOpen_chart a).measurableSet] with x hx
            exact (ENNReal.ofReal_pos.mpr ((scalarData a).positive_weight x hx)).ne')
      have hv := hw.filter_mono hac.ae_le
      filter_upwards [hv, ae_restrict_mem (isOpen_chart a).measurableSet] with x hx hxA
      intro hxK
      have hz := hx hxK
      rw [normFlat s a x hxA] at hz
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp hz) (sq_nonneg _)))
    let O := chart a ∩ baseFlat a ⁻¹' Kᶜ
    have hO : IsOpen O := (isOpen_chart a).inter (hK.isOpen_compl.preimage (baseFlat_continuous a))
    have hflat : ∀ᵐ x ∂volume.restrict (chart a), G (baseFlat a x) := by
      by_cases hne : O.Nonempty
      · obtain ⟨B,hBc,hBsub,hBexh⟩ := exists_ball_exhaustion (3*d F) (by have h := d_pos ζ hζ; omega) O hO hne
        have hBinside : ∀ k, InteriorBall a (B k) := fun k => ⟨hBc k, fun x hx => (hBsub k hx).1⟩
        have hz : ∀ᵐ x ∂volume.restrict O, liftExtension a (coefficient W a) ((baseReindex (F:=F)).symm x) = 0 := by
          rw [hBexh, ae_restrict_iUnion_iff]
          intro k
          have hscalar : scalar s a =ᵐ[volume.restrict (B k).carrier] (fun _ => 0) := by
            have hv := hsFlat.filter_mono (Measure.absolutelyContinuous_of_le
              (Measure.restrict_mono (fun x hx => (hBsub k (subset_closure hx)).1) le_rfl)).ae_le
            filter_upwards [hv, ae_restrict_mem (B k).toOpens.isOpen.measurableSet] with x hx hxB
            exact hx (hBsub k (subset_closure hxB)).2
          have ha := hlocal a (B k) (hBinside k) hscalar
          filter_upwards [Filter.eventually_all.mpr ha] with x hx
          exact decode_zero W a x hx
        have hz' := (ae_restrict_iff' hO.measurableSet).mp hz
        have ht := hz'.filter_mono (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self (s := chart a))).ae_le
        filter_upwards [ht, ae_restrict_mem (isOpen_chart a).measurableSet] with x hx hxA
        intro hxK
        rw [coefficientFlat W a x hxA, hx ⟨hxA,hxK⟩]; simp
      · exact ae_restrict_of_forall_mem (isOpen_chart a).measurableSet (fun x hx hxK =>
          (hne ⟨x,⟨hx,hxK⟩⟩).elim)
    have hlift : ∀ᵐ y ∂a.liftedMeasure, G (a.toBase y) := by
      have hw : ∀ᵐ x ∂KPChartL2.weightedMeasure (3*d F) (chart a) (weight a), G (baseFlat a x) :=
        hflat.filter_mono (withDensity_absolutelyContinuous _ _).ae_le
      rw [← lifted_measure_transport (a := a)] at hw
      have ht := (ae_map_iff hΦ.aemeasurable ((baseFlat_measurable a) hG)).mp hw
      filter_upwards [ht] with y hy
      change G (baseFlat a (fromActual (ζ := ζ) (hζ := hζ) y.val)) at hy
      rwa [baseFlat_lift] at hy
    have hb := (ae_map_iff hp.measurable.aemeasurable hG).mpr hlift
    rwa [hp.exact_pushforward] at hb
  have h := (ae_restrict_iUnion_iff (fun n => (cover.chart n).baseDomain) G).mpr hchart
  rwa [cover.covers, Measure.restrict_univ] at h

theorem weakChartData_zero_off_closed (s : BorelL2Sections F ζ hζ U R P H)
    (W : Family (U := U) (H := H)) (hs : WeakChartData s W)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsClosed K)
    (hsupp : ∀ᵐ b ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P,
      b ∉ K → squaredNorm F ζ hζ U R P H s.val b = 0) :
    ∀ᵐ b ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P, b ∉ K → normSquare W b = 0 := by
  apply zero_off_closed_of_balls s W K hK hsupp
  intro a B hB hzero
  exact weakChartData_zero_on_ball s W hs a B hB hzero

end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

end
