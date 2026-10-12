module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.HarishChandra.ZeroTensorModule

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources FourierContinuation
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem tensorHC_nonempty
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (prior : Nonempty (TensorSeed R N)) :
    Nonempty (TensorHC R N) := by
  exact TensorHCSource.tensorHC_nonempty prior
end DedekindZetaZeroFree.ThetaExpansion

end
