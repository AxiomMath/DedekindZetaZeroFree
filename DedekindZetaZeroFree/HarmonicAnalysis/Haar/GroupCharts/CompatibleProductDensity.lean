module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.GroupCharts.ImageMeasureDensity
public import DedekindZetaZeroFree.MeasureTheory.Density.CompactPositiveComparison

@[expose] public section

noncomputable section
open MeasureTheory Topology
open scoped Classical NumberField ENNReal
namespace DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2
open KPContActualSphericalRightFieldIdentification

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem exists_compatible_original_chart_density
    (chart : GroupChart F ζ hζ U R P H)
    (A : Set (KPContLocalNorm.Space (groupDimension F)))
    (hA : IsCompact A) (hAT : A ⊆ chart.T.carrier) :
    ∃ (μArch : Measure (KPSmoothLocalQuotientCharts.ArchGroup F))
      (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
      (ρ : KPContLocalNorm.Space (groupDimension F) → ℝ) (c : ℝ),
      μArch.IsHaarMeasure ∧ ν.IsHaarMeasure ∧
      Measure.map (fun p : KPSmoothLocalQuotientCharts.ArchGroup F ×
          KPFiniteCuspAtlas.FiniteCover F ζ hζ =>
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ p.1 * p.2)
          (μArch.prod ν) = R.adelicHaar ∧
      0 < ν (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) ∧
      ν (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) < ⊤ ∧
      ContinuousOn ρ chart.T.carrier ∧
      (∀ x ∈ chart.T.carrier, 0 < ρ x) ∧ 0 < c ∧
      (∀ x ∈ A, c ≤ ρ x) ∧
      ∀ S : Set (KPContLocalNorm.Space (groupDimension F)), MeasurableSet S →
        S ⊆ chart.T.carrier →
        μArch ((fun x => chart.exponential.chart (groupCoordinates F x)) '' S) =
          ∫⁻ x in S, ENNReal.ofReal (ρ x) := by
  have htransport : ∃ ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ),
      ν.IsHaarMeasure ∧
      Measure.map (fun p : KPSmoothLocalQuotientCharts.ArchGroup F ×
          KPFiniteCuspAtlas.FiniteCover F ζ hζ =>
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ p.1 * p.2)
          (R.archHaar.prod ν) = R.adelicHaar := by
    rw [← KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_finiteSubgroup_eq F ζ hζ]
    exact @PGLComplex.AdelicSlicesRaw.productHaarTransport F _ _ ζ hζ
      R.adelicHaar R.adelic_isHaar R.archHaar R.arch_isHaar
  obtain ⟨ν, hν, hprod⟩ := htransport
  letI : ν.IsHaarMeasure := hν
  obtain ⟨ρ, hρ, hp, hi⟩ := original_chart_image_measure_density chart R.archHaar R.arch_isHaar
  obtain ⟨c, hc, hb⟩ := compact_positive_density_lower_bound hA hAT hρ hp
  have hmass : 0 < ν (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) :=
    U.toOpenSubgroup.isOpen.measure_pos ν ⟨1, U.toOpenSubgroup.one_mem⟩
  have hmassT : ν (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) < ⊤ :=
    U.isCompact.measure_lt_top
  exact ⟨R.archHaar, ν, ρ, c, R.arch_isHaar, hν, hprod, hmass, hmassT, hρ, hp, hc, hb, hi⟩

end DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2

end
