module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.ReflectedCoprimeTruncation
public import DedekindZetaZeroFree.LargeSieve.Bilinear.SigmaFourDyadicExpansion

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff BigOperators

namespace DedekindZetaZeroFree.LargeSieve.ReflectedSigma4

variable {F : Type} [Field F] [NumberField F]

def unitRows (c m : Ideal (𝓞 F)) (K : ℝ) : Finset (Ideal (𝓞 F)) :=
  ({⊤} : Finset (Ideal (𝓞 F))).filter
    (fun a => Squarefree a ∧ a ⊔ m = ⊤ ∧ Bilinear.sc c a ≤ K)

end DedekindZetaZeroFree.LargeSieve.ReflectedSigma4

end
