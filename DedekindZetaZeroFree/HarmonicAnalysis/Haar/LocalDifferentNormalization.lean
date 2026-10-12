module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.LocalFields.BallAnnihilators

@[expose] public section

noncomputable section

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

local instance completionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance completionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def finiteCompletionIntegersPositiveCompacts (v : HeightOneSpectrum (𝓞 F)) :
    PositiveCompacts (v.adicCompletion F) :=
  ⟨⟨(v.adicCompletionIntegers F : Set (v.adicCompletion F)), by
    have h := isCompact_finiteCompletionBall F v 0
    rw [finiteCompletionBall_zero] at h
    exact h⟩, by
    have h : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
      have h := isOpen_finiteCompletionBall F v 0
      rw [finiteCompletionBall_zero] at h
      exact h
    rw [h.interior_eq]
    exact ⟨0, (v.adicCompletionIntegers F).zero_mem⟩⟩

@[simp] theorem coe_finiteCompletionIntegersPositiveCompacts
    (v : HeightOneSpectrum (𝓞 F)) :
    (finiteCompletionIntegersPositiveCompacts F v : Set (v.adicCompletion F)) =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := rfl

def localHalfDifferentFactor (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (Ideal.absNorm v.asIdeal : ℝ) ^ (-(localDifferentExponent F v : ℝ) / 2)

theorem localHalfDifferentFactor_pos (v : HeightOneSpectrum (𝓞 F)) :
    0 < localHalfDifferentFactor F v := by
  have h : 0 < (Ideal.absNorm v.asIdeal : ℝ) := by
    have := finiteCompletion_residueCard_gt_one F v
    exact_mod_cast (lt_trans Nat.zero_lt_one this)
  exact Real.rpow_pos_of_pos h _

def localNormalizedHaar (v : HeightOneSpectrum (𝓞 F)) :
    Measure (v.adicCompletion F) :=
  ENNReal.ofReal (localHalfDifferentFactor F v) •
    Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F v)

instance localNormalizedHaar_isAddHaarMeasure (v : HeightOneSpectrum (𝓞 F)) :
    (localNormalizedHaar F v).IsAddHaarMeasure := by
  unfold localNormalizedHaar
  apply Measure.IsAddHaarMeasure.smul
  · rw [ENNReal.ofReal_ne_zero_iff]; exact localHalfDifferentFactor_pos F v
  · exact ENNReal.ofReal_ne_top

instance localNormalizedHaar_regular (v : HeightOneSpectrum (𝓞 F)) :
    (localNormalizedHaar F v).Regular := by
  unfold localNormalizedHaar
  exact Measure.Regular.smul ENNReal.ofReal_ne_top

instance localNormalizedHaar_sigmaFinite (v : HeightOneSpectrum (𝓞 F)) :
    SigmaFinite (localNormalizedHaar F v) := by
  unfold localNormalizedHaar
  haveI : IsFiniteMeasureOnCompacts
      (ENNReal.ofReal (localHalfDifferentFactor F v) •
        Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F v)) :=
    IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top
  infer_instance

theorem localNormalizedHaar_integerRing (v : HeightOneSpectrum (𝓞 F)) :
    localNormalizedHaar F v (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
      ENNReal.ofReal (localHalfDifferentFactor F v) := by
  rw [localNormalizedHaar, Measure.smul_apply, smul_eq_mul]
  have h : Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F v)
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1 := by
    rw [← coe_finiteCompletionIntegersPositiveCompacts, Measure.addHaarMeasure_self]
  rw [h, mul_one]

theorem localNormalizedHaar_integerRing_toReal (v : HeightOneSpectrum (𝓞 F)) :
    (localNormalizedHaar F v
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))).toReal =
      localHalfDifferentFactor F v := by
  rw [localNormalizedHaar_integerRing F v,
    ENNReal.toReal_ofReal (localHalfDifferentFactor_pos F v).le]

theorem localHalfDifferentFactor_eq_norm_rpow (v : HeightOneSpectrum (𝓞 F)) :
    localHalfDifferentFactor F v =
      (localDifferentNorm F v : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hq : 0 ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    have := finiteCompletion_residueCard_gt_one F v
    exact_mod_cast (le_of_lt (lt_trans Nat.zero_lt_one this))
  rw [localHalfDifferentFactor, localDifferentNorm, Nat.cast_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul hq]
  congr 1
  ring

theorem localHalfDifferentFactor_eq_inv_sqrt (v : HeightOneSpectrum (𝓞 F)) :
    localHalfDifferentFactor F v = 1 / Real.sqrt (localDifferentNorm F v : ℝ) := by
  rw [localHalfDifferentFactor_eq_norm_rpow F v]
  have h0 : 0 ≤ (localDifferentNorm F v : ℝ) := by positivity
  rw [show (-(1 : ℝ) / 2) = -(1 / 2) by norm_num, Real.rpow_neg h0, ← Real.sqrt_eq_rpow,
    inv_eq_one_div]

end DedekindZetaZeroFree

end
