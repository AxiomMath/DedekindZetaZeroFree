module

public import DedekindZetaZeroFree.Theta.Unfolding.TensorProducts.ZeroSourceActions

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources FourierContinuation
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem tensorActions_nonempty
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (prior : Nonempty (TensorHC R N)) :
    Nonempty (TensorActions R N) := by
  exact TensorActionSource.tensorActions_nonempty prior
end DedekindZetaZeroFree.ThetaExpansion

end
