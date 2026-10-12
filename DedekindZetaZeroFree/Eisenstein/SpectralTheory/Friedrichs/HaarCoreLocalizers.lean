module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.HaarLocalizers.AveragedZeroExtension
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.HaarLocalizers.NormalBallPullback
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.Localizers.OperatorReconstruction

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree

open KPContActualFixedHaarCoreLocalizers KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry
section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

attribute [local instance 5000] KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line
attribute [local instance 5000] KPContSectorLineL2Isometry.instNormedSpaceL2Line
attribute [local instance 5000] KPContSectorLineL2Isometry.instInnerProductSpaceL2Line

 abbrev instTopologicalSpaceL2LineLocal : TopologicalSpace (L2Line F ζ hζ U R P H) :=
  (KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line F ζ hζ U R P H).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceL2LineLocal

 abbrev instAddCommMonoidL2LineLocal : AddCommMonoid (L2Line F ζ hζ U R P H) :=
  (KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line F ζ hζ U R P H).toSeminormedAddCommGroup.toAddCommMonoid

attribute [local instance 5000] instAddCommMonoidL2LineLocal

 abbrev instTopologicalSpaceHULocal : TopologicalSpace (H_U F ζ hζ U R) :=
  (inferInstance : NormedAddCommGroup (H_U F ζ hζ U R)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceHULocal

 abbrev instTopologicalSpaceHKLocal (K : Set (X_U F ζ hζ U)) :
    TopologicalSpace (H_K F ζ hζ U R P H K) :=
  (inferInstance : NormedAddCommGroup (H_K F ζ hζ U R P H K)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceHKLocal

 abbrev instAddCommMonoidHKLocal (K : Set (X_U F ζ hζ U)) :
    AddCommMonoid (H_K F ζ hζ U R P H K) :=
  (inferInstance : NormedAddCommGroup (H_K F ζ hζ U R P H K)).toSeminormedAddCommGroup.toAddCommMonoid

attribute [local instance 5000] instAddCommMonoidHKLocal

end

theorem kp_cont_actual_fixed_haar_core_localizers
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K) :
    Nonempty (KPContActualFixedHaarCoreLocalizers.Localizers F ζ hζ U R P H K hK) := by
  obtain ⟨M,hM⟩ := KPCoreChartLocalizers.actual_realization_and_localizers F ζ hζ H.totallyComplex U (H.atlas U)
  obtain ⟨C⟩ := hM K hK
  choose D hD hDb using (fun i => KPCoreChartLocalizers.cutoff_derivative_bounds (C.smooth_cutoff i) (C.compact_cutoff i))
  have hcut : ∀ i x, |C.cutoff i x| ≤ D i 0 := by
    intro i x
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hDb i 0 x
  have hphi : ∀ i x, |C.phi i x| ≤ D i 0 := by
    intro i x
    by_cases hx : x ∈ (C.chart i).O F ζ hζ H.totallyComplex U
    · obtain ⟨y,hy,rfl⟩ := hx
      have hh := hcut i y
      rw [C.cutoff_formula,Set.indicator_of_mem hy] at hh
      exact hh
    · have hz : C.phi i x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (C.support_phi i h))
      rw [hz,abs_zero]
      exact hD i 0
  have hchart := fun i => KPFixedHaarLocalizersBodies.actual_chart_measure F ζ hζ U R P H (C.chart i)
  choose T hTn hT using (fun i => KPFixedHaarNormalBallMaps.chartPullback_exists F ζ hζ U R P H
    (C.chart i) (C.cutoff i) (C.smooth_cutoff i) (C.compact_cutoff i) (C.support_cutoff i)
    (C.invariant_cutoff i) (D i 0) (hD i 0) (hcut i) (hchart i))
  choose Rmap hRn hRf using (fun i => KPFixedHaarNormalBallMaps.averagedZeroExtension_exists F ζ hζ U R P H
    K hK (C.chart i) (hchart i))
  choose B hB using (fun i => KPFixedHaarLocalizersBodies.metric_upper_bound F ζ hζ U R P H (C.chart i))
  refine ⟨{
    count := C.count
    empty_case := C.empty_case
    chart := C.chart
    open_image := C.open_image
    quotient_chart := C.quotient_chart
    quotient_chart_formula := C.quotient_chart_formula
    orbit_relation := C.orbit_relation
    line_orbit_relation := C.line_orbit_relation
    line_chart_surjective := C.line_chart_surjective
    invariant_ball := C.invariant_ball
    unitary_character := C.unitary_character
    chart_measure := hchart
    lower := fun i => ((H.disintegration U).componentWeight (C.chart i).component).toReal * (C.chart i).lower
    upper := fun i => ((H.disintegration U).componentWeight (C.chart i).component).toReal * (C.chart i).upper
    positive_lower := fun i => (KPFixedHaarLocalizersBodies.actualWeight_bounds F ζ hζ U R P H (C.chart i)).1
    density_bounds := fun i => (KPFixedHaarLocalizersBodies.actualWeight_bounds F ζ hζ U R P H (C.chart i)).2
    phi := C.phi
    nonnegative_phi := C.nonnegative_phi
    compact_phi := C.compact_phi
    support_phi := C.support_phi
    smooth_phi := C.smooth_phi
    neighborhood := C.neighborhood
    open_neighborhood := C.open_neighborhood
    covers_compact := C.covers_compact
    partition := C.partition
    cutoff := C.cutoff
    cutoff_formula := C.cutoff_formula
    smooth_cutoff := C.smooth_cutoff
    compact_cutoff := C.compact_cutoff
    support_cutoff := C.support_cutoff
    invariant_cutoff := C.invariant_cutoff
    derivativeBound := D
    nonnegative_derivativeBound := hD
    derivative_bounds := fun i k x hx => hDb i k x
    ellipticity := C.ellipticity
    metricUpper := B
    positive_ellipticity := C.positive_ellipticity
    metric_bounds := fun i x hx ξ => ⟨C.uniform_ellipticity i x (subset_closure (C.support_cutoff i hx)) ξ,
      hB i x (subset_closure (C.support_cutoff i hx)) ξ⟩
    T := T
    T_formula := hT
    Rmap := Rmap
    R_formula := hRf
    reconstruction := KPFixedHaarLocalizersBodies.finite_reconstruction F ζ hζ U R P H
      K hK C.chart C.phi C.smooth_phi C.support_phi
      (fun b hb => C.partition b (C.covers_compact hb)) C.cutoff C.cutoff_formula C.invariant_cutoff
      (fun i => D i 0) (fun i => hD i 0) hphi T hT Rmap hRf hchart
    smooth_test_image := ?_
  }⟩
  intro i f
  let fs : BorelL2Scalars F ζ hζ U R := ⟨KPContActualSectorSmoothTestModules.scalarCovered f,
    (kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H realization).scalar_continuous f |>.measurable,
    KPContActualSectorTestEmbeddings.scalar_memLp f⟩
  let ss := borelS F ζ hζ U R P H fs
  have hs : sectorLineIsometry F ζ hζ U R P H (KPContActualSectorTestEmbeddings.iota f) = mk F ζ hζ U R P H ss :=
    (kp_cont_sector_line_l2_isometry F ζ hζ U R P H).forward _ fs
      (KPContActualSectorTestEmbeddings.scalar_represented f).symm
  have hsm : IsSmoothSections F ζ hζ U R P H ss.val := by
    change IsSmoothSections F ζ hζ U R P H (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H fs.val)
    rw [(kp_cont_actual_sector_smooth_test_modules F ζ hζ μG hμG U R hR P H realization).covered_realization f]
    exact (kp_cont_actual_sector_smooth_test_modules F ζ hζ μG hμG U R hR P H realization).scalar_smooth f
  obtain ⟨hg,hgc,hgs⟩ := KPFixedHaarLocalizersBodies.smooth_cutoff_coefficient F ζ hζ U R P H
    (C.chart i) (C.cutoff i) (C.smooth_cutoff i) (C.compact_cutoff i) (C.support_cutoff i) ss.val hsm
  exact ⟨_,hg,hgc,hgs,hT i _ ss hs⟩

end DedekindZetaZeroFree

end
