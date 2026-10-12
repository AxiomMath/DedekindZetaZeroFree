module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PowerEnvelopes.Definitions
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ComplexUnits.MinimumPowerIntegrability

@[expose] public section

namespace DedekindZetaZeroFree.ThetaRawSheetEnvelope.WeightedWhittakerSheets
noncomputable section
open MeasureTheory NumberField
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

theorem weighted_archPowerMajorant_integrable (ν : Measure ℂˣ) [ν.IsHaarMeasure]
    (B s : ℝ) (hs : -(1 / 4 : ℝ) < s) (hBs : s < B) :
    Integrable (fun z : ℂˣ => ((‖z.val‖ ^ 2) ^ s) *
      archPowerMajorant B (‖z.val‖ ^ 2)) ν := by
  have hi := SheetPowerMinIntegrability.complex_units_min_powers_integrable
    (2 * (s + 1 / 4)) (2 * (s - B)) (by linarith) (by linarith) ν
  convert hi using 1
  funext z
  have hz : 0 < ‖z.val‖ := norm_pos_iff.mpr z.ne_zero
  have hz2 : 0 < ‖z.val‖ ^ 2 := pow_pos hz 2
  unfold archPowerMajorant
  rw [mul_min_of_nonneg _ _ (Real.rpow_nonneg hz2.le _)]
  change min ((‖z.val‖ ^ 2) ^ s * (‖z.val‖ ^ 2) ^ (1 / 4 : ℝ))
    ((‖z.val‖ ^ 2) ^ s * (‖z.val‖ ^ 2) ^ (-B)) = _
  rw [← Real.rpow_add hz2 s (1 / 4 : ℝ), ← Real.rpow_add hz2 s (-B)]
  rw [← Real.rpow_natCast ‖z.val‖ 2, ← Real.rpow_mul hz.le, ← Real.rpow_mul hz.le]
  congr 2 <;> ring

end
end DedekindZetaZeroFree.ThetaRawSheetEnvelope.WeightedWhittakerSheets
