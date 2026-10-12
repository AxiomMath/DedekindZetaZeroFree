module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.OutgoingZeroModeTails

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPContActualEndHaarTransport
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

theorem actual_end_coordinates_pushforward
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (A : ℝ)
    (hA : (H.atlas (KPContActualAllCuspSource.level F ζ hζ C R P H U)).threshold < A) :
    Measure.map
      (KPContActualCollarBuffer.chartLift F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H a)
      ((KPContActualChamberOutgoingAdapter.endMeasure F ζ hζ C R P H U a).restrict
        {p : KPCuspCharts.Coordinates F | A < p.2}) =
    (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P
      (KPContActualAllCuspSource.level F ζ hζ C R P H U)).restrict
      (KPContActualCollarBuffer.endSet F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H A a) := by
  let V := KPContActualAllCuspSource.level F ζ hζ C R P H U
  let atlas := H.atlas V
  let G := (atlas.cuspAtlas a.1).geometry a.2
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ V (atlas.representative a.1)
  let σ := (atlas.cuspAtlas a.1).representative a.2
  let c := KPFiniteCuspAtlas.componentMap F ζ hζ V (atlas.representative a.1)
  let e := KPFiniteCuspAtlas.endSet F Γ σ A
  let E := c '' e
  let μ := ((((volume.prod G.shapeMeasure).prod
    (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))).restrict
    {p : KPCuspCharts.Coordinates F | p.1 ∈ G.fundamentalDomain}).restrict
    {p : KPCuspCharts.Coordinates F | A < p.2})
  let q : KPCuspCharts.Coordinates F → KPCuspSiegel.OrbitQuotient F Γ :=
    fun p => KPCuspSiegel.projection F Γ (σ • KPCuspCharts.toArch F p)
  have hc : Continuous c := by
    have he : c = atlas.components ∘ Sigma.mk a.1 := by
      funext x
      exact (atlas.components_formula a.1 x).symm
    rw [he]
    exact atlas.components.continuous.comp continuous_sigmaMk
  have hci : Function.Injective c := by
    intro x y h
    have hh : atlas.components ⟨a.1,x⟩ = atlas.components ⟨a.1,y⟩ := by
      simpa only [atlas.components_formula] using h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (atlas.components.injective hh)).2
  have hco : IsOpenMap c := by
    have he : c = atlas.components ∘ Sigma.mk a.1 := by
      funext x
      exact (atlas.components_formula a.1 x).symm
    rw [he]
    exact atlas.components.isOpenMap.comp isOpenMap_sigmaMk
  have hE : MeasurableSet E :=
    ((hco _ (KPFiniteAdelicCuspEnds.component_open_end F Γ σ A))).measurableSet
  have hq : Measurable q := measurable_quotient_mk''.comp
    ((KPCuspCharts.projectiveHomeomorph F σ).continuous.measurable.comp
      (KPCuspCharts.toArch_contDiff F).continuous.measurable)
  have hcoordinate : Measure.map q μ =
      (KPFiniteCuspAtlas.quotientVolume F Γ (atlas.cuspAtlas a.1).fundamentalDomain).restrict e := by
    have hv := KPMsFixedHaar.RadialIntegrationSteps.end_volume_at_cutoff atlas a A hA.le
    rw [KPFiniteAdelicCuspEnds.cusp_end_coordinate_volume F H.totallyComplex Γ
      (KPCuspArithmetic.conjugatedStabilizer F Γ ((atlas.cuspAtlas a.1).cusp a.2) σ)
      σ A ((atlas.cuspAtlas a.1).parabolic a.2) G _ (fun _ => rfl)] at hv
    exact hv
  have hchart : KPContActualCollarBuffer.chartLift F ζ hζ V R P H a = c ∘ q := by
    funext p
    rfl
  have hsub : E ⊆ Set.range c := Set.image_subset_range _ _
  have hre : ((KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P V).restrict
      (Set.range c)).restrict E =
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P V).restrict E := by
    rw [Measure.restrict_restrict hE, Set.inter_eq_left.mpr hsub]
  change Measure.map (KPContActualCollarBuffer.chartLift F ζ hζ V R P H a)
      (((H.disintegration V).componentWeight a.1 •
        (((volume.prod G.shapeMeasure).prod
          (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))).restrict
            {p : KPCuspCharts.Coordinates F | p.1 ∈ G.fundamentalDomain})).restrict
              {p : KPCuspCharts.Coordinates F | A < p.2}) = _
  rw [Measure.restrict_smul, Measure.map_smul, hchart, ← Measure.map_map hc.measurable hq,
    hcoordinate]
  change _ = (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P V).restrict E
  rw [← hre, (H.disintegration V).component_measure a.1, Measure.restrict_smul,
    Measure.restrict_map hc.measurable hE]
  rw [show c ⁻¹' E = e from Set.preimage_image_eq _ hci]
  rw [hchart]
  exact (hc.measurable.comp hq).aemeasurable
end DedekindZetaZeroFree.KPContActualEndHaarTransport

end
