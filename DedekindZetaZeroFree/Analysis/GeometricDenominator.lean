module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPTameTransposeBaseChart.AugmentationSteps.CubeShell

theorem geometric_denominator_tsum (z c : ℂ) (hz : ‖z‖ < 1) :
    (1 - z) * (∑' k : ℕ, c * z ^ k) = c := by
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hz]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, norm_one] at hz
    exact absurd hz (by norm_num)
  field_simp

end DedekindZetaZeroFree.KPTameTransposeBaseChart.AugmentationSteps.CubeShell

end
