module

public import DedekindZetaZeroFree.Theta.Periods.OddUpperAverageVanishing

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.IdeleInsertion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)

def JointReverseAbsoluteSources.withUpperZero (C : JointReverseAbsoluteSources R N) : JointUpperVanishingSources R N where
  toJointReverseAbsoluteSources := C
  upperZero := bothUpperZero R C.constantTerm C.descent

theorem jointUpperVanishingSources_of_jointReverseAbsoluteSources (prior : Nonempty (JointReverseAbsoluteSources R N)) : Nonempty (JointUpperVanishingSources R N) := by
  rcases prior with ⟨C⟩
  exact ⟨JointReverseAbsoluteSources.withUpperZero R N C⟩
end DedekindZetaZeroFree.IdeleInsertion

end
