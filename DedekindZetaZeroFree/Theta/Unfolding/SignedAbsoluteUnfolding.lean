module

public import DedekindZetaZeroFree.Theta.Periods.UpperQuotientVanishing
public import DedekindZetaZeroFree.Theta.Unfolding.DyadicFactorizationAndSignedSeries

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem signed_unfolding (R : PrincipalMellin.ActualRecipe S η)
    (hR : RootAligned R) (N : TraceHaarTransport R)
    (prior : Nonempty (JointUpperVanishingSources R N)) : Nonempty (JointSignedUnfoldingSources R N) := by
  obtain ⟨C⟩ := prior
  exact ⟨{ toJointUpperVanishingSources := C, unfolding := SignedExpansion.signedUnfolding R C }⟩
end DedekindZetaZeroFree.ThetaExpansion
