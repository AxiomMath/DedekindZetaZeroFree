module

public import DedekindZetaZeroFree.Moments.Principal.EulerCorrectionAlgebra
public import DedekindZetaZeroFree.Moments.Probes.NormalizedPrincipalProbeExistence

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellin

noncomputable section
open scoped NumberField Classical
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]

structure ActualRecipe (S : SArithmeticData F)
    (η : RayClassCharacter F S.modulus) where
  A : SArithmeticData F
  containsOriginal : S.Sf ⊆ A.Sf
  sameModulus : A.modulus = S.modulus
  sameRoot : A.zeta12 = S.zeta12
  classKilled : Subsingleton (ClassGroup A.R)
  σ : F →+* ℂ
  traceBad : A.ContainsTraceBadPlaces
  probe : NormalizedProbe.PrincipalData A σ (sameModulus.symm ▸ η) traceBad
  normalization : NormalizedProbe.MellinNormalizationData A σ
    (sameModulus.symm ▸ η) traceBad probe
  continuation : PrincipalRayHeckeData F A.modulus (sameModulus.symm ▸ η)

namespace ActualRecipe

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

abbrev target (R : ActualRecipe S η) : RayClassCharacter F R.A.modulus :=
  R.sameModulus.symm ▸ η

def L (R : ActualRecipe S η) : ℂ → ℂ :=
  comparisonPrincipalIncompleteL F R.A R.target R.probe.principal R.continuation

def I (R : ActualRecipe S η) (Z : ℝ) : ℂ :=
  NormalizedProbe.probe R.A R.probe.coefficients R.probe.domain R.probe.W0 R.probe.W1
    (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z

def W (R : ActualRecipe S η) : ComparisonMellinWeights :=
  NormalizedProbe.principalMellinWeights R.A R.σ R.target R.traceBad R.probe

def localCorrection (R : ActualRecipe S η)
    (p : ExteriorIdealEuler.PrimeIndex R.A.cS) (s : ℂ) : ℂ :=
  Audit.Euler.principalCorrection (idealNorm p.val.val : ℂ)⁻¹
    (R.target p.val.val * comparisonRealPower (idealNorm p.val.val) (-s))
    (R.probe.coefficients.theta (R.probe.coefficients.generator p.val) ^ 6 *
      comparisonRealPower (idealNorm p.val.val) (3 - 6 * s))

def H (R : ActualRecipe S η) (s : ℂ) : ℂ :=
  ∏' p : ExteriorIdealEuler.PrimeIndex R.A.cS, R.localCorrection p s

def N (R : ActualRecipe S η) (s : ℂ) : ℂ :=
  Complex.exp ((s - 5 / 6) ^ 2) * R.H s

def G (R : ActualRecipe S η) (s : ℂ) : ℂ := R.N s / R.L s

def f (R : ActualRecipe S η) : ℝ → ℂ :=
  comparisonPrincipalSpectralTransform F R.A R.target R.probe.principal
    R.continuation R.H

def c (R : ActualRecipe S η) : ℂ :=
  comparisonPrincipalConstant F R.A R.target R.probe.principal R.continuation R.W

end ActualRecipe

end
end DedekindZetaZeroFree.PrincipalMellin
