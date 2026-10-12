module

public import DedekindZetaZeroFree.Theta.Periods.ZeroTensorRealization

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources FourierContinuation
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem tensorSeed_nonempty
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (prior : Nonempty (JointRealizedFlatSources R N)) :
    Nonempty (TensorSeed R N) := by

  exact TensorSeedSource.tensorSeed_nonempty prior
end DedekindZetaZeroFree.ThetaExpansion

end
