module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.SphericalReferences

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources FourierContinuation
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem tensorSpherical_nonempty
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (prior : Nonempty (TensorDetected R N)) :
    Nonempty (TensorSpherical R N) := by
  obtain ⟨D⟩ := prior
  exact ⟨D.spherical⟩
end DedekindZetaZeroFree.ThetaExpansion

end
