module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PowerEnvelopes.Definitions
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PositiveAxisSheetDisintegration

@[expose] public section

namespace DedekindZetaZeroFree.ThetaRawSheetEnvelope.WeightedWhittakerSheets
noncomputable section
open MeasureTheory NumberField
open scoped Classical
variable {F : Type} [Field F] [NumberField F]

def productPowerMajorant (A : SArithmeticData F) (M B : ℝ) (y : A.G) : ℝ :=
  (∏ v : A.Sf, finitePowerMajorant M ‖(y.2 v : v.val.adicCompletion F)‖) *
    ∏ w : InfinitePlace F, archPowerMajorant B (‖(y.1 w : w.Completion)‖ ^ 2)

theorem productPowerMajorant_nonneg (A : SArithmeticData F) (M B : ℝ) (y : A.G) :
    0 ≤ productPowerMajorant A M B y := by
  apply mul_nonneg
  · exact Finset.prod_nonneg fun v _ => finitePowerMajorant_nonneg M _ (norm_nonneg _)
  · exact Finset.prod_nonneg fun w _ => archPowerMajorant_nonneg B _ (sq_nonneg _)

end
end DedekindZetaZeroFree.ThetaRawSheetEnvelope.WeightedWhittakerSheets
