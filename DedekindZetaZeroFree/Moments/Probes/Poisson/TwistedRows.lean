module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.InitialIntegralIdentity

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.TwistedProbeRowDefinitions

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

abbrev TwistedRow : Type :=
  {f : PrincipalMellinComparison.Frequency D.recipe //
    f ∉ Set.range (PoissonInitialBridge.toProbeFrequency D)}

def rawIntegrand (f : PrincipalMellinComparison.Frequency D.recipe) (Z : ℝ)
    (t : ℝ × ℝ × ℝ) : ℂ :=
  ∑' a : ExteriorSquarefreeIdeal D.recipe.A.cS × D.recipe.A.Exterior ×
      D.recipe.A.Exterior × D.recipe.A.Exterior,
    NormalizedProbe.initialTripleMellinSummand D.recipe.probe
      (Scales.xScale Z) (Scales.yScale Z) Z (f, a) t

def rawRowIntegral (f : PrincipalMellinComparison.Frequency D.recipe) (Z : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, rawIntegrand D f Z t

def omittedSum (Z : ℝ) : ℂ :=
  ∑' f : TwistedRow D, rawRowIntegral D f.val Z

def omittedKernel (Z : ℝ) (t : ℝ × ℝ × ℝ) : ℂ :=
  ∑' f : TwistedRow D, rawIntegrand D f.val Z t

end

end DedekindZetaZeroFree.Quantitative.TwistedProbeRowDefinitions
