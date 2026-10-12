module

public import DedekindZetaZeroFree.Theta.Digits.SignedExteriorCoefficients

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SignedExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def actualReflectedTerm {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (Z : ℝ)
    (ξ : ThetaReflectionData.Frequency R.A) : ℂ :=
  exteriorDigitCoefficient R C m (Quotient.out ξ) *
    (Characters.L R v (Quotient.out ξ))⁻¹ *
      C.realization.H C.packet v (ThetaReflectionData.frequencyClass R.A ξ)
        (Z * ThetaReflectionData.frequencyNorm R.A ξ)

end DedekindZetaZeroFree.ThetaExpansion.SignedExpansion

end
