module

public import DedekindZetaZeroFree.Theta.Unfolding.AbsoluteOrbitExtraction

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SignedExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem absolute_extraction {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N) :
    AbsoluteExtraction R C :=
  DedekindZetaZeroFree.OrbitExpansion.absolute_extraction R C

end DedekindZetaZeroFree.ThetaExpansion.SignedExpansion

end
