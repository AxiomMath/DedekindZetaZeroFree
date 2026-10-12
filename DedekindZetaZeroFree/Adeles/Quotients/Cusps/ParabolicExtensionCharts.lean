module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.EquivariantAffineUnitCharts
public import DedekindZetaZeroFree.Adeles.Lattices.Cusps.ParabolicExtension

@[expose] public section

section
noncomputable section
namespace DedekindZetaZeroFree.KPCuspGenuineGeometry

theorem chartOutput_of_extension
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D₀ : KPCuspChart.ExtensionData F S)
    (hdisc : DiscreteTopology (KPCuspChart.translationLattice F D₀.L).toIntSubmodule)
    (hlattice : letI := hdisc; IsZLattice ℝ (KPCuspChart.translationLattice F D₀.L).toIntSubmodule) :
    ∃ (D : KPCuspCharts.ParabolicData F S), Nonempty (KPCuspCharts.ChartOutput F hF S D) := by
  obtain ⟨G⟩ := KPCuspChart.finite_affine_bundle_atlas F hF _ D₀ hdisc hlattice
  obtain ⟨V⟩ := KPCuspChart.normalized_finite_section F hF _ D₀ hdisc hlattice G
  obtain ⟨R⟩ := KPCuspChart.radial_quotient_disintegration F hF _ D₀ G V
  let D : KPCuspCharts.ParabolicData F
      S := {
    L := D₀.L
    E := D₀.E
    inclusion := D₀.inclusion
    ratio := D₀.ratio
    integralUnits := D₀.integralUnits
    unitIndex := D₀.unitIndex
    injective := D₀.injective
    surjective := D₀.surjective
    exact := D₀.exact
    upper := D₀.upper
    unipotentFormula := D₀.unipotentFormula
    ratioFormula := D₀.ratioFormula
  }
  let atlas : KPCuspCharts.BundleAtlas F hF _ D G.torusAction := {
    projection := G.atlas.projection
    continuous_projection := G.atlas.continuous_projection
    projection_formula := G.atlas.projection_formula
    lift := G.atlas.lift
    continuous_lift := G.atlas.continuous_lift
    lift_formula := G.atlas.lift_formula
    orbit_equivalence := G.atlas.orbit_equivalence
    chartCount := G.atlas.chartCount
    positive_chartCount := G.atlas.positive_chartCount
    shapeLift := G.atlas.shapeLift
    open_shapeLift := G.atlas.open_shapeLift
    nonempty_shapeLift := G.atlas.nonempty_shapeLift
    small_shapeLift := G.atlas.small_shapeLift
    baseOpen := G.atlas.baseOpen
    open_baseOpen := G.atlas.open_baseOpen
    baseOpen_formula := G.atlas.baseOpen_formula
    cover := G.atlas.cover
    baseChart := G.atlas.baseChart
    baseChart_formula := G.atlas.baseChart_formula
    coarseChart := G.atlas.coarseChart
    coarseChart_formula := G.atlas.coarseChart_formula
    transitions := G.atlas.transitions
  }
  let O : KPCuspCharts.ChartOutput F hF _ D := {
    positive_dimension := KPCuspCharts.positive_dimension F hF
    lattice := ⟨hdisc, hlattice⟩
    compact_torus := G.compact_torus
    compact_base := G.compact_base
    finite_isotropy := G.finite_isotropy
    torusAction := G.torusAction
    torusAction_formula := G.torusAction_formula
    compact_cross := G.compact_cross
    crossAction := G.crossAction
    crossAction_formula := G.crossAction_formula
    atlas := atlas
    actual_action := KPCuspCharts.actual_affine_action F hF _ D
    unipotent_action := KPCuspCharts.actual_unipotent_action F hF _ D
    metric_invariant := by
      intro g A _ _ p v
      exact KPCuspCharts.affine_metric_invariant F hF D.E D.integralUnits
        (D.ratio g) (A 0 1 / A 1 1) p v
    smooth_transitions := by
      intro g A _ _
      exact KPCuspCharts.affine_contDiff F hF D.E D.integralUnits
        (D.ratio g) (A 0 1 / A 1 1)
    density_formula := KPCuspCharts.volumeDensity_toArch F
    shapeMeasure := V.shapeMeasure
    haar_shapeMeasure := V.haar_shapeMeasure
    archVolume_formula := V.archVolume_formula
    measure_invariant := V.measure_invariant
    fundamentalDomain := V.fundamentalDomain
    measurable_fundamentalDomain := V.measurable_fundamentalDomain
    isFundamentalDomain := V.isFundamentalDomain
    sectionMeasure := V.sectionMeasure
    sectionMeasure_formula := V.sectionMeasure_formula
    finite_sectionMeasure := V.finite_sectionMeasure
    positive_sectionMeasure := V.positive_sectionMeasure
    radialPresentation := R.radialPresentation
    radialPresentation_formula := R.radialPresentation_formula
    quotientVolume_formula := R.quotientVolume_formula
    highPresentation := R.highPresentation
    highPresentation_formula := R.highPresentation_formula
    highVolume_formula := R.highVolume_formula
  }
  exact ⟨D, ⟨O⟩⟩

end DedekindZetaZeroFree.KPCuspGenuineGeometry

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPCuspMonodromy

theorem finite_adelic_cusp_charts
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hcompact : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (hopen : IsOpen (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (g : KPFiniteComponents.FinitePGL2 F)
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q) :
    let Γ := KPFiniteComponents.arithmeticStabilizer F U g
    let S := KPCuspArithmetic.conjugatedStabilizer F Γ q σ
    ∃ (D : KPCuspCharts.ParabolicData F S),
      Nonempty (KPCuspCharts.ChartOutput F hF S D) := by
  obtain ⟨D, hdisc, hlattice⟩ :=
    KPCuspFiniteArithmetic.finite_adelic_parabolic_extension_lattice
      F hF U hcompact hopen g q σ hσ
  exact KPCuspGenuineGeometry.chartOutput_of_extension F hF _ D hdisc hlattice

end DedekindZetaZeroFree.KPCuspMonodromy

end

end
