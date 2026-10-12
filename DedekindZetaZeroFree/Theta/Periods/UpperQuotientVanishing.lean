module

public import DedekindZetaZeroFree.Theta.Unfolding.ReverseAbsoluteConvergence
public import DedekindZetaZeroFree.Theta.Unfolding.UpperVanishingCertificates

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem both_upper_averages_zero (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (prior : Nonempty (JointReverseAbsoluteSources R N)) : Nonempty (JointUpperVanishingSources R N) := by
  exact IdeleInsertion.jointUpperVanishingSources_of_jointReverseAbsoluteSources R N prior

end DedekindZetaZeroFree.ThetaExpansion
