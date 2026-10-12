module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarMeromorphicFamilies
public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothGerms.UniformCompactTaylorRealization

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SharedSource
open MomentSources EisensteinSmoothGerms
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem selected_realization_exists
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R}
    (B : JointRootAlignedSources R N) : Nonempty (Realization R B.sources) := by
  obtain ⟨C, ⟨H⟩⟩ := ThetaExpansion.selected_scalar_source_exists  R B
  obtain ⟨T, _⟩ := scalar_family_realization_constructed H
  exact ⟨T⟩

end DedekindZetaZeroFree.SharedSource

end
