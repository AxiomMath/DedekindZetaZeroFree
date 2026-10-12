module

public import DedekindZetaZeroFree.Analysis.MellinVerticalIntegral

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Vendor.Subquadratic

def gaussianRegulator (f : ℂ → ℂ) (ε : ℝ) (s : ℂ) : ℂ :=
  f s * Complex.exp ((ε : ℂ) * s ^ 2)

end DedekindZetaZeroFree.LargeSieve.Vendor.Subquadratic

end
