module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.SectionSpaces.BoundedLiftingAndDescent

@[expose] public section

section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.CoreChartLocalizers.Reconstruction

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

theorem average_local_lift (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K)
    (P : FrameComparison F ζ hζ hF U A M C)
    (B : LocalOperators F ζ hζ hF U A M C P)
    (v : H F ζ hζ hF U A) (i : Fin C.count) :
    (C.chart i).average F ζ hζ hF U (B.T i v) =ᵐ[
      volume.restrict (Metric.ball 0 (C.chart i).radius)]
      fun x => (C.phi i ((C.chart i).toBase F ζ hζ hF U x) : ℂ) *
        (P.phase i x : ℂ) * (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ) := by

  have hball_mem : ∀ (g : (C.chart i).G F ζ hζ hF U) (x : E (C.chart i).n),
      (C.chart i).orthogonal g x ∈ Metric.ball 0 (C.chart i).radius ↔
        x ∈ Metric.ball 0 (C.chart i).radius := by
    intro g x
    simp only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]

  have hbase : ∀ (g : (C.chart i).G F ζ hζ hF U) (x : E (C.chart i).n),
      x ∈ (C.chart i).extendedDomain →
      (C.chart i).toBase F ζ hζ hF U ((C.chart i).orthogonal g x) =
        (C.chart i).toBase F ζ hζ hF U x := by
    intro g x hx
    unfold Chart.toBase
    rw [(C.chart i).equivariance g x hx]
    apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative (C.chart i).component))
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    exact MulAction.mem_orbit_iff.mpr ⟨g.val, rfl⟩

  have hmp : ∀ g : (C.chart i).G F ζ hζ hF U,
      MeasurePreserving ((C.chart i).orthogonal g)
        (volume.restrict (Metric.ball 0 (C.chart i).radius))
        (volume.restrict (Metric.ball 0 (C.chart i).radius)) := by
    intro g
    have he : ((C.chart i).orthogonal g) ⁻¹' Metric.ball 0 (C.chart i).radius =
        Metric.ball 0 (C.chart i).radius := by
      ext x
      exact hball_mem g x
    have hm : MeasurePreserving ((C.chart i).orthogonal g)
        (volume : Measure (E (C.chart i).n)) volume :=
      LinearIsometryEquiv.measurePreserving ((C.chart i).orthogonal g)
    have hr := hm.restrict_preimage (s := Metric.ball 0 (C.chart i).radius)
      Metric.isOpen_ball.measurableSet
    rw [he] at hr
    exact hr

  have havg_congr : ∀ {f k : E (C.chart i).n → ℂ},
      f =ᵐ[volume.restrict (Metric.ball 0 (C.chart i).radius)] k →
      (C.chart i).average F ζ hζ hF U f =ᵐ[volume.restrict (Metric.ball 0 (C.chart i).radius)]
        (C.chart i).average F ζ hζ hF U k := by
    intro f k hfk
    have hg : ∀ g : (C.chart i).G F ζ hζ hF U,
        (fun x => f ((C.chart i).orthogonal g x)) =ᵐ[
          volume.restrict (Metric.ball 0 (C.chart i).radius)]
          fun x => k ((C.chart i).orthogonal g x) := fun g =>
      (hmp g).quasiMeasurePreserving.ae_eq_comp hfk
    filter_upwards [Filter.eventually_all.mpr hg] with x hx
    by_cases hball : x ∈ Metric.ball (0 : E (C.chart i).n) (C.chart i).radius
    · simp only [Chart.average, Set.indicator_of_mem hball]
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      rw [hx g]
    · simp only [Chart.average, Set.indicator_of_notMem hball]

  have hsub : Metric.ball (0 : E (C.chart i).n) (C.chart i).radius ⊆
      cube (C.chart i).n (C.chart i).a :=
    (subset_closure).trans ((C.chart i).closed_ball_in_cube.trans interior_subset)
  have hle : volume.restrict (Metric.ball 0 (C.chart i).radius) ≤
      volume.restrict (cube (C.chart i).n (C.chart i).a) :=
    Measure.restrict_mono hsub le_rfl
  have hcube : (fun x => B.T i v x) =ᵐ[volume.restrict (cube (C.chart i).n (C.chart i).a)]
      (Metric.ball 0 (C.chart i).radius).indicator
        (fun x => (C.phi i ((C.chart i).toBase F ζ hζ hF U x) : ℂ) *
          (P.phase i x : ℂ) * (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ)) :=
    B.T_formula i v
  have h1 : (fun x => B.T i v x) =ᵐ[volume.restrict (Metric.ball 0 (C.chart i).radius)]
      (Metric.ball 0 (C.chart i).radius).indicator
        (fun x => (C.phi i ((C.chart i).toBase F ζ hζ hF U x) : ℂ) *
          (P.phase i x : ℂ) * (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ)) :=
    (MeasureTheory.ae_mono hle) hcube
  have h2 : (Metric.ball 0 (C.chart i).radius).indicator
        (fun x => (C.phi i ((C.chart i).toBase F ζ hζ hF U x) : ℂ) *
          (P.phase i x : ℂ) * (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ))
      =ᵐ[volume.restrict (Metric.ball 0 (C.chart i).radius)]
        (fun x => (C.phi i ((C.chart i).toBase F ζ hζ hF U x) : ℂ) *
          (P.phase i x : ℂ) * (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ)) :=
    (MeasureTheory.ae_restrict_mem Metric.isOpen_ball.measurableSet).mono
      (fun x hx => Set.indicator_of_mem hx _)
  refine (havg_congr (h1.trans h2)).trans ?_

  have hphase : ∀ᵐ x ∂volume.restrict (Metric.ball 0 (C.chart i).radius),
      ∀ g : (C.chart i).G F ζ hζ hF U,
        (P.phase i ((C.chart i).orthogonal g x) : ℂ) =
          ((C.chart i).rho F ζ hζ hF U g : ℂ) * (P.phase i x : ℂ) :=
    Filter.eventually_all.mpr (fun g => P.phase_equivariance i g)
  filter_upwards [hphase, MeasureTheory.ae_restrict_mem Metric.isOpen_ball.measurableSet]
    with x hphx hxball
  rw [Chart.average, Set.indicator_of_mem hxball]
  have hxext : x ∈ (C.chart i).extendedDomain :=
    (C.chart i).closed_ball_in_extension (subset_closure hxball)
  have hterm : ∀ g : (C.chart i).G F ζ hζ hF U,
      (↑(((C.chart i).rho F ζ hζ hF U g)⁻¹) : ℂ) *
          ((fun x => (C.phi i ((C.chart i).toBase F ζ hζ hF U x) : ℂ) *
            (P.phase i x : ℂ) * (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ))
              ((C.chart i).orthogonal g x)) =
        (C.phi i ((C.chart i).toBase F ζ hζ hF U x) : ℂ) * (P.phase i x : ℂ) *
          (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ) := by
    intro g
    have hb := hbase g x hxext
    show (↑(((C.chart i).rho F ζ hζ hF U g)⁻¹) : ℂ) *
        ((C.phi i ((C.chart i).toBase F ζ hζ hF U ((C.chart i).orthogonal g x)) : ℂ) *
          (P.phase i ((C.chart i).orthogonal g x) : ℂ) *
          (v ((C.chart i).toBase F ζ hζ hF U ((C.chart i).orthogonal g x)) : ℂ)) =
        (C.phi i ((C.chart i).toBase F ζ hζ hF U x) : ℂ) * (P.phase i x : ℂ) *
          (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ)
    rw [hb, hphx g, Units.val_inv_eq_inv_val]
    have hg : ((C.chart i).rho F ζ hζ hF U g : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  have hsum : (∑ g : (C.chart i).G F ζ hζ hF U,
      (↑(((C.chart i).rho F ζ hζ hF U g)⁻¹) : ℂ) *
        ((fun x => (C.phi i ((C.chart i).toBase F ζ hζ hF U x) : ℂ) *
          (P.phase i x : ℂ) * (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ))
            ((C.chart i).orthogonal g x))) =
      (Fintype.card ((C.chart i).G F ζ hζ hF U) : ℂ) *
        ((C.phi i ((C.chart i).toBase F ζ hζ hF U x) : ℂ) * (P.phase i x : ℂ) *
          (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ)) := by
    rw [Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  rw [hsum, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

end DedekindZetaZeroFree.CoreChartLocalizers.Reconstruction

end

end

section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.CoreChartLocalizers.Reconstruction

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

theorem extend_local_lift (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K)
    (P : FrameComparison F ζ hζ hF U A M C)
    (B : LocalOperators F ζ hζ hF U A M C P)
    (v : H F ζ hζ hF U A) (i : Fin C.count)
    (hlocal : ∀ᵐ x ∂(quotientMeasure F ζ hζ hF U A).restrict K,
      x ∈ (C.chart i).O F ζ hζ hF U →
        B.R i (B.T i v) x = (C.phi i x : ℂ) • v x) :
    B.R i (B.T i v) =ᵐ[(quotientMeasure F ζ hζ hF U A).restrict K]
      fun x => (C.phi i x : ℂ) • v x := by
  filter_upwards [hlocal, B.R_zero_extension i (B.T i v)] with x hx hz
  by_cases hxO : x ∈ (C.chart i).O F ζ hζ hF U
  · exact hx hxO
  · have hphi : C.phi i x = 0 := by
      by_contra h
      exact hxO (C.support_phi i (subset_tsupport (C.phi i) h))
    rw [hz hxO, hphi]
    simp

end DedekindZetaZeroFree.CoreChartLocalizers.Reconstruction

end

end

section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.CoreChartLocalizers.Reconstruction

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

set_option maxHeartbeats 800000 in
theorem descend_local_lift (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (hK : MeasurableSet K) (C : FiniteCutoffs F ζ hζ hF U A K)
    (P : FrameComparison F ζ hζ hF U A M C)
    (B : LocalOperators F ζ hζ hF U A M C P)
    (v : H F ζ hζ hF U A) (i : Fin C.count)
    (haverage : (C.chart i).average F ζ hζ hF U (B.T i v) =ᵐ[
      volume.restrict (Metric.ball 0 (C.chart i).radius)]
      fun x => (C.phi i ((C.chart i).toBase F ζ hζ hF U x) : ℂ) *
        (P.phase i x : ℂ) * (v ((C.chart i).toBase F ζ hζ hF U x) : ℂ)) :
    ∀ᵐ x ∂(quotientMeasure F ζ hζ hF U A).restrict K,
      x ∈ (C.chart i).O F ζ hζ hF U →
        B.R i (B.T i v) x = (C.phi i x : ℂ) • v x := by
  let base : E (C.chart i).n → X F ζ hζ U := (C.chart i).toBase F ζ hζ hF U
  let ball : Set (E (C.chart i).n) := Metric.ball 0 (C.chart i).radius
  let O : Set (X F ζ hζ U) := (C.chart i).O F ζ hζ hF U
  let ν : Measure (E (C.chart i).n) :=
    (Fintype.card ((C.chart i).G F ζ hζ hF U) : ℝ≥0∞)⁻¹ •
      (volume.restrict ball).withDensity (fun x => ENNReal.ofReal ((C.chart i).weight x))
  have hAvg_ae : ∀ᵐ x ∂volume.restrict ball,
      (C.chart i).average F ζ hζ hF U (B.T i v) x =
        (C.phi i (base x) : ℂ) * (P.phase i x : ℂ) * (v (base x) : ℂ) := haverage
  have hball_ae : ∀ᵐ x ∂volume.restrict ball, base x ∈ K →
      B.R i (B.T i v) (base x) = (C.phi i (base x) : ℂ) • v (base x) := by
    filter_upwards [B.R_formula i (B.T i v), hAvg_ae] with x hR hAvg
    intro hxK
    rw [hR hxK, hAvg]
    have hz : ((P.phase i x)⁻¹ : ℂˣ) *
        ((C.phi i (base x) : ℂ) * (P.phase i x : ℂ) * (v (base x) : ℂ))
        = (C.phi i (base x) : ℂ) * (v (base x) : ℂ) := by
      rw [Units.val_inv_eq_inv_val]
      rw [show (C.phi i (base x) : ℂ) * ↑(P.phase i x) * ↑(v (base x))
          = ↑(P.phase i x) * ((C.phi i (base x) : ℂ) * ↑(v (base x))) by ring]
      rw [inv_mul_cancel_left₀ (Units.ne_zero (P.phase i x))]
    have hmem : (C.phi i (base x) : ℂ) * (v (base x) : ℂ) ∈ V F ζ hζ U := by
      have h := (V F ζ hζ U).smul_mem (C.phi i (base x) : ℂ) (v (base x)).2
      simpa using h
    rw [hz, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := V F ζ hζ U)
      (v := ⟨(C.phi i (base x) : ℂ) * (v (base x) : ℂ), hmem⟩)]
    apply Subtype.ext
    simp

  have hνac : ν ≪ volume.restrict ball :=
    (Measure.smul_absolutelyContinuous (μ := (volume.restrict ball).withDensity
        (fun x => ENNReal.ofReal ((C.chart i).weight x)))
      (c := (Fintype.card ((C.chart i).G F ζ hζ hF U) : ℝ≥0∞)⁻¹)).trans
      (withDensity_absolutelyContinuous (volume.restrict ball) _)
  have hν_ae : ∀ᵐ x ∂ν, base x ∈ K →
      B.R i (B.T i v) (base x) = (C.phi i (base x) : ℂ) • v (base x) :=
    hball_ae.filter_mono hνac.ae_le
  have hbase_aemeas : AEMeasurable base ν := by
    letI : BorelSpace (X F ζ hζ U) := ⟨rfl⟩
    have hc : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U
        (A.representative (C.chart i).component)) := by
      have hh := A.components.continuous.comp (continuous_sigmaMk (i := (C.chart i).component))
      simpa only [Function.comp_def, A.components_formula] using hh
    have hproj : Continuous (KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U
          (A.representative (C.chart i).component))) := continuous_quot_mk
    have hb : AEMeasurable base (volume.restrict ball) := by
      have h := ((hc.comp hproj).comp_continuousOn
        ((C.chart i).smooth_coordinates.continuousOn.mono
          (Set.Subset.trans subset_closure (C.chart i).closed_ball_in_extension))).aemeasurable
            Metric.isOpen_ball.measurableSet (μ := volume)
      exact h
    exact (hb.mono_ac (withDensity_absolutelyContinuous (volume.restrict ball) _)).smul_measure _
  have hO_ae : ∀ᵐ x ∂(quotientMeasure F ζ hζ hF U A).restrict O, x ∈ K →
      B.R i (B.T i v) x = (C.phi i x : ℂ) • v x := by
    have hphi : Measurable (C.phi i) := by
      have hs : Measurable (fun p : Fin A.componentCount × KPFiniteCuspAtlas.SymmetricSpace F =>
          C.phi i (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative p.1)
            (KPCuspSiegel.projection F _ p.2))) :=
        measurable_from_prod_countable_right (fun j => (C.smooth_phi i j).continuous.measurable)
      have hh := hs.comp (M.measurable_component.prodMk M.measurable_lift)
      simpa only [Function.comp_def, M.lift_formula] using hh
    let μ := quotientMeasure F ζ hζ hF U A
    let bad : Set (X F ζ hζ U) :=
      {x | ¬ (B.R i (B.T i v) x = (C.phi i x : ℂ) • v x)}
    have hbad : NullMeasurableSet bad (μ.restrict K) := by
      have hr := Lp.aestronglyMeasurable (B.R i (B.T i v))
      have hv := (Lp.aestronglyMeasurable v).restrict (s := K)
      have hp : AEStronglyMeasurable (fun x => (C.phi i x : ℂ)) (μ.restrict K) :=
        (Complex.measurable_ofReal.comp hphi).aestronglyMeasurable
      exact (hr.nullMeasurableSet_eq_fun (hp.smul hv)).compl
    have hbadK : NullMeasurableSet (bad ∩ K) μ :=
      (nullMeasurableSet_restrict hK.nullMeasurableSet).mp hbad
    have hmap : Measure.map base ν = μ.restrict O := C.chart_measure i
    have hnull : ν (base ⁻¹' (bad ∩ K)) = 0 := by
      have hh := ae_iff.mp hν_ae
      simpa only [not_imp, Set.preimage_setOf_eq, Set.inter_def, bad,
        Set.mem_setOf_eq, and_comm] using hh
    have hzero : (μ.restrict O) (bad ∩ K) = 0 := by
      rw [← hmap, Measure.map_apply₀ hbase_aemeas]
      · exact hnull
      · rw [hmap]
        exact hbadK.mono Measure.restrict_le_self
    apply ae_iff.mpr
    simpa only [not_imp, Set.inter_def, bad, Set.mem_setOf_eq, and_comm] using hzero
  rw [ae_restrict_iff' hK]
  refine ae_iff.mpr ?_
  have hset : {x : X F ζ hζ U |
        ¬ (x ∈ K → x ∈ O → B.R i (B.T i v) x = (C.phi i x : ℂ) • v x)}
      = {x | x ∈ K ∧ x ∈ O ∧ ¬ (B.R i (B.T i v) x = (C.phi i x : ℂ) • v x)} := by
    ext x; simp only [Set.mem_setOf_eq, not_imp]
  rw [hset]
  have h0 : ((quotientMeasure F ζ hζ hF U A).restrict O)
      {x | ¬ (x ∈ K → B.R i (B.T i v) x = (C.phi i x : ℂ) • v x)} = 0 := ae_iff.mp hO_ae
  refine nonpos_iff_eq_zero.mp ?_
  calc (quotientMeasure F ζ hζ hF U A)
        {x | x ∈ K ∧ x ∈ O ∧ ¬ (B.R i (B.T i v) x = (C.phi i x : ℂ) • v x)}
      = (quotientMeasure F ζ hζ hF U A)
          ({x | x ∈ K ∧ ¬ (B.R i (B.T i v) x = (C.phi i x : ℂ) • v x)} ∩ O) := by
        congr 1; ext x; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
    _ ≤ ((quotientMeasure F ζ hζ hF U A).restrict O)
          {x | x ∈ K ∧ ¬ (B.R i (B.T i v) x = (C.phi i x : ℂ) • v x)} :=
        Measure.le_restrict_apply _ _
    _ ≤ ((quotientMeasure F ζ hζ hF U A).restrict O)
          {x | ¬ (x ∈ K → B.R i (B.T i v) x = (C.phi i x : ℂ) • v x)} :=
        measure_mono (fun x hx => by simp only [Set.mem_setOf_eq] at hx ⊢; tauto)
    _ = 0 := h0

end DedekindZetaZeroFree.CoreChartLocalizers.Reconstruction

end

end

section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory

namespace DedekindZetaZeroFree.CoreChartLocalizers.Reconstruction

theorem finite_partition_restriction {Y : Type*} [MeasurableSpace Y]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [MeasurableSpace W] [BorelSpace W]
    {ι : Type*} [Fintype ι] (μ : Measure Y) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {K : Set Y} (hK : MeasurableSet K) (phi : ι → Y → ℂ)
    (hpartition : ∀ x ∈ K, ∑ i, phi i x = 1)
    (v : Lp W p μ) (w : ι → Lp W p (μ.restrict K))
    (hw : ∀ i, w i =ᵐ[μ.restrict K] fun x => phi i x • v x) :
    LpToLpRestrictCLM Y W ℂ μ p K v = ∑ i, w i := by
  rw [Lp.ext_iff]

  have hrestrict : LpToLpRestrictCLM Y W ℂ μ p K v =ᵐ[μ.restrict K] ⇑v :=
    LpToLpRestrictCLM_coeFn ℂ K v

  have hsum : ⇑(∑ i, w i) =ᵐ[μ.restrict K] fun x => ∑ i, phi i x • v x := by
    refine (Lp.coeFn_finsetSum (Finset.univ : Finset ι) w).trans ?_
    refine (eventuallyEq_sum fun i _ => hw i).trans ?_
    exact Filter.EventuallyEq.of_eq (by funext x; rw [Finset.sum_apply])

  have hone : (fun x => ∑ i, phi i x • v x) =ᵐ[μ.restrict K] ⇑v := by
    filter_upwards [ae_restrict_mem hK] with x hx
    rw [← Finset.sum_smul, hpartition x hx, one_smul]
  exact hrestrict.trans (hone.symm.trans hsum.symm)

end DedekindZetaZeroFree.CoreChartLocalizers.Reconstruction

end

end

section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.CoreChartLocalizers

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

theorem local_reconstruction (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (hK : MeasurableSet K) (C : FiniteCutoffs F ζ hζ hF U A K)
    (P : FrameComparison F ζ hζ hF U A M C)
    (B : LocalOperators F ζ hζ hF U A M C P) (v : H F ζ hζ hF U A) :
    LpToLpRestrictCLM (X F ζ hζ U) (V F ζ hζ U) ℂ
      (quotientMeasure F ζ hζ hF U A) 2 K v =
        ∑ i, B.R i (B.T i v) := by
  refine Reconstruction.finite_partition_restriction
    (quotientMeasure F ζ hζ hF U A) 2 hK
    (fun i x => (C.phi i x : ℂ)) ?_ v (fun i => B.R i (B.T i v)) ?_
  · intro x hx
    have hp := C.partition x (C.covers_compact hx)
    exact_mod_cast hp
  · intro i
    apply Reconstruction.extend_local_lift F ζ hζ hF U A M C P B v i
    apply Reconstruction.descend_local_lift F ζ hζ hF U A M hK C P B v i
    exact Reconstruction.average_local_lift F ζ hζ hF U A M C P B v i

end DedekindZetaZeroFree.CoreChartLocalizers

end

end
