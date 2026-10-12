module

public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.EquivariantScalarAndCotangentData
public import DedekindZetaZeroFree.Analysis.SmoothFunctions.CompactOpenHolomorphyAndMeromorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorCoordinateNullEquivalence

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualCotangentMeasurableFamilies KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContActualCotangentChartRestriction
open KPContActualSectorChartEquivariantInputs KPContSectorLineL2Isometry
open KPContLocalNorm KPContSectorSmoothFramesSupport
open KPContActualCotangentCountableShrinking KPContCotangentActualGenuineTwistIsotropy
open KPContSectorPhaseComponentCharts

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

def BallInside (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F)) : Prop :=
  IsCompact (closure B.carrier) ∧
    closure B.carrier ⊆ (baseReindex (F := F)).symm ⁻¹' omega a

def scalar (s : BorelL2Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : Space (3 * d F)) : ℂ :=
  liftExtension a (sectionFields s.val a) ((baseReindex (F := F)).symm x)

def coordinateW (W : Family (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (x : Space (3 * d F))
    (j : Fin (3 * d F)) : ℂ :=
  let p := (baseReindex (F := F)).symm x
  let ik := (coefficientIndex (F := F)).symm j
  let v := liftExtension a (coefficient W a) p
  ![(Real.exp (-p (ik.1, 2)) : ℂ) * v (ik.1, 1),
    (Real.exp (-p (ik.1, 2)) : ℂ) * v (ik.1, 2), v (ik.1, 0)] ik.2

private lemma measurable_fromActual :
    Measurable (fromActual (F := F) (ζ := ζ) (hζ := hζ)) := by
  unfold KPContActualSectorChartEquivariantInputs.fromActual
    KPContCotangentActualOverlap.labeledAInv
  fun_prop

private lemma chart_eq_preimage (a : ActualChart (U := U) (H := H)) :
    chart a = (baseReindex (F := F)).symm ⁻¹' omega a := by
  ext x
  simp only [Set.mem_preimage, KPContActualSectorChartEquivariantInputs.chart,
    KPContCotangentOverlapRationalBranches.omega,
    KPContActualSectorChartEquivariantInputs.toActual]

private lemma toBase_eq (a : ActualChart (U := U) (H := H)) (y : a.domain) :
    a.toBase y = (H.atlas U).components ⟨a.component, Quotient.mk _ y.val⟩ := by
  rw [KPContActualCotangentCountableShrinking.ShrunkChart.toBase]
  simp only [KPFiniteCuspAtlas.componentMap, (H.atlas U).components_formula]
  rfl

private lemma sectionNorm_toBase (a : ActualChart (U := U) (H := H))
    (u : Sections F ζ hζ U R P H) (y : a.domain) :
    sectionNorm F ζ hζ U R P H u (a.toBase y) = ‖(u a.component).val y.val‖ := by
  rw [toBase_eq (a := a) y]
  exact sectionNorm_component F ζ hζ U R P H u a.component y.val

private lemma continuous_toActual :
    Continuous (toActual (F := F) (ζ := ζ) (hζ := hζ)) := by
  unfold KPContActualSectorChartEquivariantInputs.toActual
    KPContCotangentActualOverlap.labeledA
  fun_prop

private lemma measurable_toActual :
    Measurable (toActual (F := F) (ζ := ζ) (hζ := hζ)) :=
  continuous_toActual.measurable

private lemma isOpen_chart (a : ActualChart (U := U) (H := H)) : IsOpen (chart a) :=
  a.domain_open.preimage continuous_toActual

private lemma toActual_fromActual (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
    toActual (ζ := ζ) (hζ := hζ) (fromActual (ζ := ζ) (hζ := hζ) y) = y := by
  simp only [KPContActualSectorChartEquivariantInputs.toActual,
    KPContActualSectorChartEquivariantInputs.fromActual, LinearIsometryEquiv.symm_apply_apply]
  funext k
  simp [KPContCotangentActualOverlap.labeledA, KPContCotangentActualOverlap.labeledAInv]

private theorem sectionFields_apply_actual (s : Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    sectionFields s a x = (s a.component).val (labeledA (placeEquiv F ζ hζ) x.val) := by
  have hcoe : (isotropyChart a).coefficient s x.val =
      (KPCuspGenuineMonodromy.chi F ζ hζ ((isotropyChart a).splitting x.val) : ℂ) *
        (s a.component).val
          ((isotropyChart a).kind.representative •
            labeledA (isotropyChart a).places x.val) := rfl
  rw [sectionFields, hcoe]
  simp [isotropyChart, KPContCotangentActualOverlap.ChartKind.representative]

private lemma scalar_eq_on_chart (s : BorelL2Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : Space (3 * d F)) (hx : x ∈ chart a) :
    scalar s a x = (s.val a.component).val (toActual (ζ := ζ) (hζ := hζ) x) := by
  have hx' : (baseReindex (F := F)).symm x ∈ omega a := by
    rw [chart_eq_preimage] at hx; exact hx
  unfold scalar liftExtension
  rw [dif_pos hx', sectionFields_apply_actual]
  rfl

private lemma sectionNorm_eq_zero_measurableSet (u : Sections F ζ hζ U R P H)
    (hu : ∀ i, Measurable (u i).val) :
    MeasurableSet {b | sectionNorm F ζ hζ U R P H u b = 0} := by
  have hsq : Measurable (squaredNorm F ζ hζ U R P H u) :=
    squaredNorm_measurable F ζ hζ U R P H u hu
  have hset : {b | sectionNorm F ζ hζ U R P H u b = 0} =
      {b | KPContSectorLineL2Isometry.squaredNorm F ζ hζ U R P H u b = 0} := by
    ext b
    simp only [Set.mem_setOf_eq]
    rw [KPContSectorLineL2Isometry.squaredNorm]
    constructor
    · intro h; rw [h]; simp
    · intro h
      simp only [ENNReal.ofReal_eq_zero] at h
      have h2 : sectionNorm F ζ hζ U R P H u b ^ 2 = 0 := le_antisymm h (sq_nonneg _)
      exact sq_eq_zero_iff.mp h2
  rw [hset]
  exact measurableSet_eq_fun hsq measurable_const

theorem scalar_ae_of_mk_eq (s t : BorelL2Sections F ζ hζ U R P H)
    (hst : mk F ζ hζ U R P H s = mk F ζ hζ U R P H t)
    (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F))
    (hB : BallInside a B) :
    (fun x => scalar s a x) =ᵐ[volume.restrict B.carrier] (fun x => scalar t a x) := by
  obtain ⟨-, hBsub⟩ := hB
  have hBchart : B.carrier ⊆ chart a := fun x hx => hBsub (subset_closure hx)

  have hnorm0 : squaredNorm F ζ hζ U R P H (s.val - t.val)
      =ᵐ[KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U] 0 :=
    (mk_eq_mk_iff F ζ hζ U R P H s t).mp hst
  have hsn : sectionNorm F ζ hζ U R P H (s.val - t.val)
      =ᵐ[KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U] 0 := by
    filter_upwards [hnorm0] with b hb
    simp only [KPContSectorLineL2Isometry.squaredNorm, Pi.zero_apply,
      ENNReal.ofReal_eq_zero] at hb
    exact sq_eq_zero_iff.mp (le_antisymm hb (sq_nonneg _))

  have hu : ∀ i, Measurable ((s.val - t.val) i).val := by
    intro i
    have h1 := s.property.1 i
    have h2 := t.property.1 i
    have he : ((s.val - t.val) i).val =
        fun x => (s.val i).val x - (t.val i).val x := by
      funext x; simp
    rw [he]; exact h1.sub h2
  have hP := every_shrunkChart_properties F ζ hζ U R P H a
  have hmeas : MeasurableSet {b | sectionNorm F ζ hζ U R P H (s.val - t.val) b = 0} :=
    sectionNorm_eq_zero_measurableSet (s.val - t.val) hu
  have hbase : ∀ᵐ b ∂((KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict
      a.baseDomain), sectionNorm F ζ hζ U R P H (s.val - t.val) b = 0 :=
    ae_mono Measure.restrict_le_self hsn
  rw [← hP.exact_pushforward] at hbase
  have hlift : ∀ᵐ y ∂a.liftedMeasure,
      sectionNorm F ζ hζ U R P H (s.val - t.val) (a.toBase y) = 0 :=
    (ae_map_iff hP.measurable.aemeasurable hmeas).mp hbase

  have hcoeff : (fun y : a.domain => (s.val a.component).val y.val)
      =ᵐ[a.liftedMeasure] (fun y : a.domain => (t.val a.component).val y.val) := by
    filter_upwards [hlift] with y hy
    rw [sectionNorm_toBase] at hy
    have hsub : ((s.val - t.val) a.component).val y.val =
        (s.val a.component).val y.val - (t.val a.component).val y.val := by simp
    rw [hsub, norm_eq_zero, sub_eq_zero] at hy
    exact hy

  have hΦ : Measurable (fun y : a.domain => fromActual (ζ := ζ) (hζ := hζ) y.val) :=
    measurable_fromActual.comp measurable_subtype_coe
  have hwm : ∀ᵐ x ∂Measure.map (fun y : a.domain => fromActual (ζ := ζ) (hζ := hζ) y.val)
        a.liftedMeasure,
      (s.val a.component).val (toActual (ζ := ζ) (hζ := hζ) x) =
        (t.val a.component).val (toActual (ζ := ζ) (hζ := hζ) x) := by
    refine (ae_map_iff hΦ.aemeasurable ?_).mpr ?_
    · exact measurableSet_eq_fun ((s.property.1 a.component).comp measurable_toActual)
        ((t.property.1 a.component).comp measurable_toActual)
    · filter_upwards [hcoeff] with y hy
      simpa only [Function.comp_apply, toActual_fromActual] using hy
  rw [lifted_measure_transport (a := a)] at hwm

  have hwe : AEMeasurable (weight a) (volume.restrict (chart a)) :=
    (scalarData a).smooth_weight.continuousOn.aemeasurable (isOpen_chart a).measurableSet
  have hvol_chart : (fun x => (s.val a.component).val (toActual (ζ := ζ) (hζ := hζ) x))
      =ᵐ[volume.restrict (chart a)]
      (fun x => (t.val a.component).val (toActual (ζ := ζ) (hζ := hζ) x)) := by
    refine (withDensity_ae_eq (ENNReal.measurable_ofReal.comp_aemeasurable hwe) ?_).mp ?_
    · filter_upwards [self_mem_ae_restrict (isOpen_chart a).measurableSet] with x hx
      exact (ENNReal.ofReal_pos.mpr ((scalarData a).positive_weight x hx)).ne'
    · rw [KPChartL2.weightedMeasure] at hwm; exact hwm
  have hchart_scalar : (fun x => scalar s a x) =ᵐ[volume.restrict (chart a)]
      (fun x => scalar t a x) := by
    filter_upwards [hvol_chart, self_mem_ae_restrict (isOpen_chart a).measurableSet]
      with x hx hxc
    rw [scalar_eq_on_chart s a x hxc, scalar_eq_on_chart t a x hxc]
    exact hx
  exact ae_mono (Measure.restrict_mono_set volume hBchart) hchart_scalar

end DedekindZetaZeroFree.KPContActualSectorCoordinateNullEquivalence

end
