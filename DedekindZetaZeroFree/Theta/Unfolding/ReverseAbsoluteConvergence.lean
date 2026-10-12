module

public import DedekindZetaZeroFree.Theta.Profiles.LogarithmicRegularityAndSmoothing
public import DedekindZetaZeroFree.Theta.Unfolding.ForwardOrbitAbsoluteIntegrability

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem reverse_joint_absolute (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (prior : Nonempty (JointSameResidueProfileSources R N)) : Nonempty (JointReverseAbsoluteSources R N) := by
  obtain ⟨C⟩ := prior
  exact ⟨DedekindZetaZeroFree.OrbitFrequencies.jointReverseAbsoluteSources R C⟩

end DedekindZetaZeroFree.ThetaExpansion
