module

public import DedekindZetaZeroFree.Moments.Reflected.RankOneExpansion

@[expose] public section

namespace DedekindZetaZeroFree.MomentSources
noncomputable section
variable {F : Type} [Field F] [NumberField F]

theorem source_exists
    (S : SArithmeticData F) (η : RayClassCharacter F S.modulus)
    (hη : η.IsPrincipal) (P : PrincipalRayHeckeData F S.modulus η) :
    ∃ R : PrincipalMellin.ActualRecipe S η,
      RootAligned R ∧ Nonempty (SelectedMomentSource R) :=
  ThetaExpansion.selected_rank_one_expansion S η hη P

end
end DedekindZetaZeroFree.MomentSources
