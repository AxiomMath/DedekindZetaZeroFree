module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGLHyperbolic.CompactStabilizer

@[expose] public section

namespace DedekindZetaZeroFree.KPCompactStabilizerHaarSources

open MeasureTheory

theorem hyperbolic_volume_properties (d : ℕ) :
    IsFiniteMeasureOnCompacts (KPArch.hyperbolicVolume d) ∧
      (KPArch.hyperbolicVolume d).IsOpenPosMeasure ∧
      SMulInvariantMeasure (G d) (X d) (KPArch.hyperbolicVolume d) := by
  classical
  have hc : Continuous (KPArch.volumeDensity d) := by
    unfold KPArch.volumeDensity KPArch.height
    apply continuous_finsetProd
    intro i _
    exact ((Real.continuous_exp.comp ((continuous_apply i).snd)).inv₀
      (fun z => Real.exp_ne_zero _)).pow 2
  have hp (z : X d) : 0 < KPArch.volumeDensity d z := by
    unfold KPArch.volumeDensity
    apply Finset.prod_pos
    intro i _
    exact sq_pos_of_pos (inv_pos.mpr (Real.exp_pos _))
  haveI : IsLocallyFiniteMeasure (KPArch.hyperbolicVolume d) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hc
  refine ⟨inferInstance, ?_, ?_⟩
  · exact (withDensity_absolutelyContinuous' hc.measurable.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun z => (ENNReal.ofReal_pos.mpr (hp z)).ne')).isOpenPosMeasure
  · refine ⟨fun g s hs => ?_⟩
    choose h hh using fun i => Matrix.ProjGenLinGroup.mk_surjective (g i)
    have hg : g = fun i => Matrix.ProjGenLinGroup.mk (h i) := by
      funext i
      exact (hh i).symm
    have he : (fun z : X d => g • z) = KPArch.productAction d h := by
      funext z
      rw [hg]
      exact KPArithmeticAction.productProjectiveAction_mk d h z
    rw [he]
    have hm := congrArg (fun μ : Measure (X d) => μ s)
      (KPArch.hyperbolicVolume_invariant d h)
    rw [Measure.map_apply (KPArch.productAction_contDiff d h).continuous.measurable hs] at hm
    exact hm

end DedekindZetaZeroFree.KPCompactStabilizerHaarSources
