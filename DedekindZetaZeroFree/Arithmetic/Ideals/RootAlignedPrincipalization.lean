module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SixthRootAlignment

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources

theorem root_aligned_recipe_exists {F : Type} [Field F] [NumberField F]
     (S : SArithmeticData F)
    (η : RayClassCharacter F S.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F S.modulus η) :
    ∃ R : PrincipalMellin.ActualRecipe S η, RootAligned R :=
  aligned_recipe_exists S η hη P
end DedekindZetaZeroFree.ThetaExpansion
