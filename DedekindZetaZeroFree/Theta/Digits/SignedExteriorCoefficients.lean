module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.ProductAverageCoefficients

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SignedExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem exterior_digit_coefficient {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (m : ThetaReflectionData.Row R.A)
    (D : ThetaBranch.RowFactorization R.A R.probe.allowed m) (x : Fˣ) :
    (∀ d, Function.HasFiniteMulSupport (exteriorDigitFactor R C m x d)) ∧
    exteriorDigitCoefficient R C m x =
      ThetaBranch.exteriorCoefficient R.A R.probe.allowed R.σ (Characters.psi R) m D x := by
  exact ⟨fun d => DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits.finite_support R C m x d,
    DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits.coefficient_exact R C m D x⟩

end DedekindZetaZeroFree.ThetaExpansion.SignedExpansion

end
