module

public import DedekindZetaZeroFree.Arithmetic.Ideals.InverseNormPowerSums
public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorFinsets

@[expose] public section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.ReflectedTails

def primalSummand (F : Type*) [Field F] [NumberField F]
    (g : ℝ → ℂ) (T : ℝ) (d b : Ideal (𝓞 F)) : ℂ :=
  if b = ⊥ then 0 else g ((Ideal.absNorm d : ℝ) * (Ideal.absNorm b : ℝ) / T)

def primalTail (F : Type*) [Field F] [NumberField F]
    (g : ℝ → ℂ) (T : ℝ) (D : Finset (Ideal (𝓞 F)))
    (a : Ideal (𝓞 F) → ℂ) : ℂ :=
  ∑ d ∈ D, a d * ∑' b : Ideal (𝓞 F), primalSummand F g T d b

end DedekindZetaZeroFree.LargeSieve.ReflectedTails

end
