module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.PositiveLineInversion

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.Vendor

def originMellinH (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  Complex.Gammaℂ s * originMellinQ h s

end DedekindZetaZeroFree.LargeSieve.Vendor

end
