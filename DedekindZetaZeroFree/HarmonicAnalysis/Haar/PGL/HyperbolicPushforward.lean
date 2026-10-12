module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGL.CompactStabilizerLift
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGL.HyperbolicVolume
public import DedekindZetaZeroFree.Geometry.PGL.IwasawaTrivialization

@[expose] public section

namespace DedekindZetaZeroFree.KPCompactStabilizerHaarSources

noncomputable section
open scoped NNReal ENNReal
open MeasureTheory

theorem arch_haar_pushforward_hyperbolic (d : ℕ) (μ : Measure (G d))
    [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧
      Measure.map (fun g : G d => g • o d) μ =
        (c : ℝ≥0∞) • KPArch.hyperbolicVolume d := by
  obtain ⟨e, heOrbit, heFiber⟩ := product_iwasawa_homeomorph d
  obtain ⟨hfinite, hpositive, hinvariant⟩ := hyperbolic_volume_properties d
  let ν : Measure (G d) :=
    Measure.map e.symm ((KPArch.hyperbolicVolume d).prod (stabilizerHaar d))
  have : ν.IsHaarMeasure := compact_fiber_lift_isHaar d e heFiber
    (KPArch.hyperbolicVolume d) hfinite hpositive hinvariant
    (stabilizerHaar d) inferInstance inferInstance
  refine ⟨Measure.haarScalarFactor μ ν,
    Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν, ?_⟩
  have hμ := Measure.isMulLeftInvariant_eq_smul μ ν
  have horbit : Measure.map (fun g : G d => g • o d) ν =
      KPArch.hyperbolicVolume d := by
    have hcomp : (fun p : X d × K d => e.symm p • o d) = Prod.fst := by
      funext p
      rw [← heOrbit (e.symm p), e.apply_symm_apply]
    change Measure.map (fun g : G d => g • o d)
      (Measure.map e.symm ((KPArch.hyperbolicVolume d).prod (stabilizerHaar d))) = _
    have hm : Measurable (fun g : G d => g • o d) :=
      (show Continuous (fun g : G d => g • o d) from
        continuous_id.smul continuous_const).measurable
    rw [Measure.map_map hm e.symm.measurable]
    simp only [Function.comp_def, hcomp, Measure.map_fst_prod,
      measure_univ, one_smul]
  calc
    Measure.map (fun g : G d => g • o d) μ =
        Measure.map (fun g : G d => g • o d) (Measure.haarScalarFactor μ ν • ν) :=
      congrArg (Measure.map (fun g : G d => g • o d)) hμ
    _ = (Measure.haarScalarFactor μ ν : ℝ≥0∞) • KPArch.hyperbolicVolume d := by
      have hm : AEMeasurable (fun g : G d => g • o d) ν :=
        (show Continuous (fun g : G d => g • o d) from
          continuous_id.smul continuous_const).measurable.aemeasurable
      rw [Measure.map_smul _ hm, horbit]
      rfl

end

end DedekindZetaZeroFree.KPCompactStabilizerHaarSources
