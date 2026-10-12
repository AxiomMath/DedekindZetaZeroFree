module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace DedekindZetaZeroFree.ThetaRawSheetEnvelope.WeightedWhittakerSheets
noncomputable section

def finitePowerMajorant (M r : ℝ) : ℝ :=
  if r ≤ M then Real.rpow r (1 / 4 : ℝ) else 0

def archPowerMajorant (B r : ℝ) : ℝ :=
  min (Real.rpow r (1 / 4 : ℝ)) (Real.rpow r (-B))

theorem finitePowerMajorant_nonneg (M r : ℝ) (hr : 0 ≤ r) :
    0 ≤ finitePowerMajorant M r := by
  unfold finitePowerMajorant
  split_ifs
  · exact Real.rpow_nonneg hr _
  · exact le_refl 0

theorem archPowerMajorant_nonneg (B r : ℝ) (hr : 0 ≤ r) :
    0 ≤ archPowerMajorant B r := by
  exact le_min (Real.rpow_nonneg hr _) (Real.rpow_nonneg hr _)

end
end DedekindZetaZeroFree.ThetaRawSheetEnvelope.WeightedWhittakerSheets
