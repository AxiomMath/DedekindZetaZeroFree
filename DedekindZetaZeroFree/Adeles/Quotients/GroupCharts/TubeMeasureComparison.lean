module

public import DedekindZetaZeroFree.Adeles.Quotients.GroupCharts.FiniteLevelTubeDomination

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

def chartTube (chart : GroupChart F ζ hζ U R P H)
    (p : KPContLocalNorm.Space (groupDimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    KPSmoothLocalQuotientCharts.X F ζ hζ :=
  KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (chart.groupLift p.1 * p.2)

theorem group_chart_full_tube_haar_domination
    (chart : GroupChart F ζ hζ U R P H)
    (A : Set (KPContLocalNorm.Space (groupDimension F)))
    (hA : IsCompact A) (hAT : A ⊆ chart.T.carrier) :
    ∃ (μArch : Measure (KPSmoothLocalQuotientCharts.ArchGroup F))
      (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) (C : ℝ),
      μArch.IsHaarMeasure ∧ ν.IsHaarMeasure ∧
      Measure.map (fun p : KPSmoothLocalQuotientCharts.ArchGroup F ×
          KPFiniteCuspAtlas.FiniteCover F ζ hζ =>
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ p.1 * p.2)
          (μArch.prod ν) = R.adelicHaar ∧
      0 < ν (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) ∧
      ν (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) < ⊤ ∧
      0 < C ∧
      Measure.map (chartTube chart)
        ((volume.restrict A).prod
          (ν.restrict (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ)))) ≤
        ENNReal.ofReal C • R.quotientHaar := by
  exact actual_original_chart_tube_domination chart A hA hAT

end DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2

end
