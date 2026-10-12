module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.ResidualRadialCovariance
public import DedekindZetaZeroFree.Theta.Profiles.GaussianSmoothing

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem mellin_gaussian (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (prior : Nonempty (JointResidualConstantTermSources R N)) : Nonempty (JointMellinGaussianSources R N) := by
  obtain ⟨C⟩ := prior
  exact ⟨{ toJointResidualConstantTermSources := C, mellin := GaussianSmoothing.mellinGaussian C.transport C.packet }⟩

end DedekindZetaZeroFree.ThetaExpansion
