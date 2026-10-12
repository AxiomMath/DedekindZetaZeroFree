module

public import DedekindZetaZeroFree.Theta.Whittaker.Sources.CovariantExistence

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources FourierContinuation.NonDegenerate
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem detected_finite_covariant_dictionary_exists
    (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
    (prior : Nonempty (Generated R N)) :
    ∃ D : FiniteCovariant R N, D.coreMap (D.selected D.probe) ≠ 0 := by
  suffices h : Nonempty (FiniteCovariant R N) by
    obtain ⟨D⟩ := h
    exact ⟨D, D.toDictionary.image_ne⟩
  obtain ⟨D⟩ := prior
  obtain ⟨E⟩ := FourierContinuation.LiteralSource.current_covariant_nonempty  R D.aligned N
  exact ⟨E.toFiniteCovariant⟩

end DedekindZetaZeroFree.ThetaExpansion

end
