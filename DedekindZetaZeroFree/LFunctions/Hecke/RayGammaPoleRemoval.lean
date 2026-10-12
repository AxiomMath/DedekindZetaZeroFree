module

public import DedekindZetaZeroFree.Analysis.EntireDividedDifference
public import DedekindZetaZeroFree.Theta.Profiles.RayParityFourierMellin

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.AbelianQuotient.RayGammaPoleRemoval

def completedEntirePart (h E : ℂ → ℂ) (A B : ℂ) : ℂ → ℂ :=
  fun s ↦ h s * E s + A * entireDividedDifference h 1 s -
    B * entireDividedDifference h 0 s

theorem completed_pole_decomposition (h E : ℂ → ℂ) (h0 : h 0 = 0)
    (A B s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    h s * (E s + A / (s - 1) - B / s) =
      completedEntirePart h E A B s + (A * h 1) / (s - 1) := by
  rw [completedEntirePart, entireDividedDifference_of_ne h 1 s hs1,
    entireDividedDifference_of_zero h 0 s h0 hs0]
  field_simp
  ring

end DedekindZetaZeroFree.AbelianQuotient.RayGammaPoleRemoval

end
