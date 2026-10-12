module

public import DedekindZetaZeroFree.Arithmetic.Ideals.InverseNormPowerSums
public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorFinsets

@[expose] public section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.ReflectedTails

def dualCutoffSummand (F : Type*) [Field F] [NumberField F]
    (k : ℝ → ℂ) (T L : ℝ) (d b : Ideal (𝓞 F)) : ℂ :=
  if b ≠ ⊥ ∧ L < (Ideal.absNorm b : ℝ)
  then k (T * (Ideal.absNorm b : ℝ) / (Ideal.absNorm d : ℝ)) else 0

def dualCutoffTail (F : Type*) [Field F] [NumberField F]
    (k : ℝ → ℂ) (T L : ℝ) (D : Finset (Ideal (𝓞 F)))
    (a : Ideal (𝓞 F) → ℂ) : ℂ :=
  ∑ d ∈ D, a d * (T / (Ideal.absNorm d : ℝ) : ℂ) *
    ∑' b : Ideal (𝓞 F), dualCutoffSummand F k T L d b

end DedekindZetaZeroFree.LargeSieve.ReflectedTails

end
