module

public import DedekindZetaZeroFree.Metaplectic.Weil.QuadraticFourierOperatorsAndPhases
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalDifferentNormalization

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology ENNReal

namespace DedekindZetaZeroFree.FiniteOscillatoryStabilization

 local instance haarMeasurable (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

 local instance haarBorel (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem finiteTraceHaar_eq_localNormalizedHaar_of_integerVolume
    {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (hvolume : PoissonS.integerVolume F v = localHalfDifferentFactor F v) :
    A.finiteTraceHaar v = localNormalizedHaar F v := by
  let μ : Measure (v.adicCompletion F) := Measure.addHaar
  let K := finiteCompletionIntegersPositiveCompacts F v
  have hμ : μ = μ K • Measure.addHaarMeasure K := Measure.addHaarMeasure_unique μ K
  have hO : (K : Set (v.adicCompletion F)) = {x | ‖x‖ ≤ (1 : ℝ)} := by
    rw [coe_finiteCompletionIntegersPositiveCompacts]
    ext x
    exact ⟨norm_le_one_of_mem_adicCompletionIntegers v,
      mem_adicCompletionIntegers_of_norm_le_one v⟩
  have hp : μ K ≠ 0 :=
    (MeasureTheory.Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hf : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  change (ENNReal.ofReal (PoissonS.integerVolume F v) /
    μ {x | ‖x‖ ≤ (1 : ℝ)}) • μ = _
  rw [← hO]
  conv_lhs => arg 2; rw [hμ]
  rw [smul_smul, localNormalizedHaar, hvolume]
  congr 1
  rw [ENNReal.div_mul_cancel hp hf]

end DedekindZetaZeroFree.FiniteOscillatoryStabilization

end
