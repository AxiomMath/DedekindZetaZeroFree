module

public import DedekindZetaZeroFree.Theta.Whittaker.Sources.LocalLineExistence

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources FourierContinuation
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem tensorFiniteLines_nonempty
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (prior : Nonempty (TensorSpherical R N)) :
    Nonempty (TensorFiniteLines R N) := by
  obtain ⟨D⟩ := FourierContinuation.LiteralSource.current_local_lines_nonempty  R hR N
  exact ⟨D.toTensorFiniteLines⟩
end DedekindZetaZeroFree.ThetaExpansion

end
