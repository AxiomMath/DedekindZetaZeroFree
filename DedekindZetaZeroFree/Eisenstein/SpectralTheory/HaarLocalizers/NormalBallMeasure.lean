module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.HaarLocalizers.LineRestriction

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal Pointwise
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPFixedHaarLocalizersBodies

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

theorem actual_chart_measure
    (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U)) :
    Measure.map (C.toBase F ζ hζ H.totallyComplex U)
      ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball 0 C.radius)).withDensity
          (fun x => ENNReal.ofReal
            (((H.disintegration U).componentWeight C.component).toReal * C.weight x))) =
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict
        (C.O F ζ hζ H.totallyComplex U) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := by
    change Countable (Fin 2 → Fin 2 → F); infer_instance
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Function.Injective.countable Units.val_injective
  letI : Countable (KPCuspArithmetic.PGL2 F) :=
    Function.Surjective.countable Matrix.ProjGenLinGroup.mk_surjective
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative C.component)
  let μ := KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)
  let π := KPCuspSiegel.projection F Γ
  let j := KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative C.component)
  let S := C.coordinates '' Metric.ball (0 : KPCoreChartLocalizers.E C.n) C.radius
  let T := MulAction.stabilizer Γ C.center
  letI : Fintype T := C.finite_stabilizer
  letI : MeasurableConstSMul Γ (KPFiniteCuspAtlas.SymmetricSpace F) :=
    ⟨fun g => (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F g.val).measurable⟩
  letI : SMulInvariantMeasure Γ (KPFiniteCuspAtlas.SymmetricSpace F) μ := by
    constructor; intro g s hs
    have hp := KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F g.val
    change (KPArch.hyperbolicVolume _) ((fun z => g.val • z) ⁻¹' s) = _
    rw [← Measure.map_apply hp.measurable hs, hp.map_eq]
  have hball : Metric.ball (0 : KPCoreChartLocalizers.E C.n) C.radius ⊆ C.extendedDomain :=
    subset_closure.trans C.closed_ball_in_extension
  have hS : IsOpen S := by
    have hi : IsOpen ((Subtype.val : C.extendedDomain → KPCoreChartLocalizers.E C.n) ⁻¹'
        Metric.ball 0 C.radius) := Metric.isOpen_ball.preimage continuous_subtype_val
    have hh := (KPCoreChartLocalizers.Chart.coordinates_open_embedding F ζ hζ H.totallyComplex U C).isOpenMap _ hi
    have heq : (Set.restrict C.extendedDomain C.coordinates) ''
        ((Subtype.val : C.extendedDomain → KPCoreChartLocalizers.E C.n) ⁻¹' Metric.ball 0 C.radius) = S := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩; exact ⟨x.val,hx,rfl⟩
      · rintro ⟨x,hx,rfl⟩; exact ⟨⟨x,hball hx⟩,hx,rfl⟩
    rwa [heq] at hh
  have hinv (g : T) : (g.val : Γ) • S = S := by
    change (fun z => g.val.val • z) '' S = S
    have heq : (fun z => g.val.val • z) '' S =
        C.coordinates '' (C.orthogonal g '' Metric.ball 0 C.radius) := by
      ext z
      constructor
      · rintro ⟨_, ⟨x,hx,rfl⟩,rfl⟩
        exact ⟨C.orthogonal g x, ⟨x,hx,rfl⟩, C.equivariance g x (hball hx)⟩
      · rintro ⟨_, ⟨x,hx,rfl⟩,rfl⟩
        exact ⟨C.coordinates x, ⟨x,hx,rfl⟩, (C.equivariance g x (hball hx)).symm⟩
    rw [heq]
    congr 1
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hy
    · intro hx
      refine ⟨(C.orthogonal g).symm x, ?_, (C.orthogonal g).apply_symm_apply x⟩
      simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
  have hsep (g : Γ) (z : KPFiniteCuspAtlas.SymmetricSpace F) (hz : z ∈ S)
      (hgz : g • z ∈ S) : g ∈ T := by
    obtain ⟨x,hx,rfl⟩ := hz
    obtain ⟨y,hy,heq⟩ := hgz
    exact C.separated g x y (hball hx) (hball hy) heq.symm
  have hlocal := CoreChartLocalizers.CutoffConstruction.finite_isotropy_quotient_measure
    μ T ((H.atlas U).cuspAtlas C.component).fundamentalDomain S
    ((H.atlas U).cuspAtlas C.component).measurable_fundamentalDomain hS.measurableSet
    ((H.atlas U).cuspAtlas C.component).isFundamentalDomain hinv hsep
  have hj : Topology.IsOpenEmbedding j := by
    have he : j = (H.atlas U).components ∘ Sigma.mk C.component := by
      funext z; exact ((H.atlas U).components_formula C.component z).symm
    rw [he]
    exact (H.atlas U).components.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk
  letI : OpensMeasurableSpace (KPCuspSiegel.OrbitQuotient F Γ) := ⟨by
    exact MeasurableSpace.generateFrom_le (fun s hs =>
      measurableSet_quotient.mpr ((hs.preimage (show Continuous π from continuous_quotient_mk')).measurableSet))⟩
  letI : BorelSpace (KPFiniteCuspAtlas.rawXU F ζ hζ U) := ⟨rfl⟩
  have hjm : Measurable j := hj.continuous.measurable
  have hπm : Measurable π := measurable_quotient_mk''
  let ν := (volume.restrict (Metric.ball (0 : KPCoreChartLocalizers.E C.n) C.radius)).withDensity
    (fun x => ENNReal.ofReal (C.weight x))
  have hcoord : AEMeasurable C.coordinates ν :=
    ((C.smooth_coordinates.continuousOn.mono hball).aemeasurable Metric.isOpen_ball.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hb : C.toBase F ζ hζ H.totallyComplex U = j ∘ π ∘ C.coordinates := rfl
  have hbm : AEMeasurable (C.toBase F ζ hζ H.totallyComplex U) ν := by
    rw [hb]
    exact (hjm.comp hπm).comp_aemeasurable hcoord
  change Measure.map π ((Fintype.card T : ℝ≥0∞)⁻¹ • μ.restrict S) =
    (KPFiniteCuspAtlas.quotientVolume F Γ
      ((H.atlas U).cuspAtlas C.component).fundamentalDomain).restrict (π '' S) at hlocal
  have hm : Measure.map (C.toBase F ζ hζ H.totallyComplex U)
      ((Fintype.card T : ℝ≥0∞)⁻¹ • ν) =
      Measure.map j ((KPFiniteCuspAtlas.quotientVolume F Γ
        ((H.atlas U).cuspAtlas C.component).fundamentalDomain).restrict (π '' S)) := by
    rw [Measure.map_smul _ hbm, hb, ← Function.comp_assoc,
      ← AEMeasurable.map_map_of_aemeasurable (hjm.comp hπm).aemeasurable hcoord,
      C.coordinate_volume,
      ← Measure.map_map hjm hπm,
      ← Measure.map_smul _ hjm.aemeasurable,
      ← Measure.map_smul _ hπm.aemeasurable, hlocal]
  have hO : C.O F ζ hζ H.totallyComplex U = j '' (π '' S) := by
    simp only [KPCoreChartLocalizers.Chart.O, hb, S, Set.image_image, Function.comp_assoc]
    rfl
  have hpre : j ⁻¹' C.O F ζ hζ H.totallyComplex U = π '' S := by
    rw [hO, Set.preimage_image_eq _ hj.injective]
  have ho := C.open_image F ζ hζ H.totallyComplex U
  have hsub : C.O F ζ hζ H.totallyComplex U ⊆ Set.range j := by
    rw [hO]; exact Set.image_subset_range _ _
  have hweight : (fun x => ENNReal.ofReal
      (((H.disintegration U).componentWeight C.component).toReal * C.weight x)) =
      (H.disintegration U).componentWeight C.component • (fun x => ENNReal.ofReal (C.weight x)) := by
    funext x
    rw [ENNReal.ofReal_mul (ENNReal.toReal_nonneg),
      ENNReal.ofReal_toReal (ne_of_lt ((H.disintegration U).finite_componentWeight C.component))]
    rfl
  rw [hweight, withDensity_smul' _ _ (ne_of_lt ((H.disintegration U).finite_componentWeight C.component)),
    smul_comm]
  rw [Measure.map_smul _ (hbm.smul_measure _), hm]
  rw [← hpre, ← Measure.restrict_map hjm ho.measurableSet, ← Measure.restrict_smul,
    ← (H.disintegration U).component_measure C.component,
    Measure.restrict_restrict_of_subset hsub]

end DedekindZetaZeroFree.KPFixedHaarLocalizersBodies

namespace DedekindZetaZeroFree.KPFixedHaarNormalBallMaps

open KPContActualFixedHaarCoreLocalizers

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

theorem actual_chart_measure (C : Chart F ζ hζ U R P H) :
    Measure.map (C.toBase F ζ hζ H.totallyComplex U)
      ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball 0 C.radius)).withDensity
          (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x))) =
      (muU F ζ hζ U R P).restrict (C.O F ζ hζ H.totallyComplex U) := by
  simpa only [actualWeight, muU] using
    KPFixedHaarLocalizersBodies.actual_chart_measure F ζ hζ U R P H C

end DedekindZetaZeroFree.KPFixedHaarNormalBallMaps

end
