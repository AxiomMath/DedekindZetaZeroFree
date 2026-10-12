module

public import DedekindZetaZeroFree.Moments.Probes.SignedUnfoldingAndAngularCancellation

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources

theorem selected_moment_source_of_certified_packet {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η) (C : CertifiedPacket R) :
    RootAligned R ∧ Nonempty (SelectedMomentSource R) :=
  momentSource_of_certified_packet R C
end DedekindZetaZeroFree.ThetaExpansion
