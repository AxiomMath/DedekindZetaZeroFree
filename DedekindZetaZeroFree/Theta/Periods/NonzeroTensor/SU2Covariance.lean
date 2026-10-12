module

public import DedekindZetaZeroFree.Theta.Whittaker.Sources.CovariantExistence

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources FourierContinuation.NonDegenerate
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem detected_complex_covariant_dictionary_exists
    (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
    (prior : Nonempty (FiniteCovariant R N)) :
    ∃ D : ComplexCovariant R N, D.coreMap (D.selected D.probe) ≠ 0 := by
  suffices h : Nonempty (ComplexCovariant R N) by
    obtain ⟨D⟩ := h
    exact ⟨D, D.toDictionary.image_ne⟩
  obtain ⟨D⟩ := prior
  exact FourierContinuation.LiteralSource.current_covariant_nonempty  R D.aligned N

end DedekindZetaZeroFree.ThetaExpansion

end
