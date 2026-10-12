module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.StandardIntegralConvergence
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdelicCharts.TraceBoxFubini

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.FullSourceExhaustion
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local notation "W" => KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
  (KPCubicCoverConstruction.adelicW F ζ hζ)
open _root_.DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual renaming actual_standard_integrable → actual_standard_integrable
open _root_.DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual renaming section_signed_weyl → section_signed_weyl
open _root_.DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual renaming rational → rational

theorem adelicBox_monotone : Monotone (TraceBox.adelicBox F) := by
  intro S T hST a ha
  change a.2 ∈ Set.range (KPAdditiveHaar.chartMap F S) at ha
  change a.2 ∈ Set.range (KPAdditiveHaar.chartMap F T)
  rw [KPAdditiveHaar.chartMap_range] at ha ⊢
  intro q hq
  exact ha q (fun h => hq (hST h))

theorem adelicBox_iUnion : (⋃ E, TraceBox.adelicBox F E) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  have hfin : {q | ¬ a.2 q ∈ q.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp a.2.property
  apply Set.mem_iUnion.mpr
  refine ⟨hfin.toFinset, ?_⟩
  change a.2 ∈ Set.range (KPAdditiveHaar.chartMap F hfin.toFinset)
  rw [KPAdditiveHaar.chartMap_range]
  intro q hq
  by_contra hbad
  exact hq ((Set.Finite.mem_toFinset hfin).mpr hbad)

theorem adelicBox_measurable (E : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) :
    MeasurableSet (TraceBox.adelicBox F E) := by
  have ho := (KPAdditiveHaar.chartMap_isOpenEmbedding F E).isOpen_range
  have hc : Continuous (fun a : A F => a.2) := continuous_snd
  have hb : IsOpen (TraceBox.adelicBox F E) := ho.preimage hc
  exact hb.measurableSet

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.FullSourceExhaustion

end
