module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalSourceCriterion
public import DedekindZetaZeroFree.Theta.Unfolding.AbsolutelyConvergentExpansion

@[expose] public section

namespace DedekindZetaZeroFree

theorem principal_mellin_zero_free
    (F : Type) [Field F] [NumberField F]
    (S : SArithmeticData F)
    (η : RayClassCharacter F S.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F S.modulus η) :
    ∀ s : ℂ, (5999 / 6000 : ℝ) < s.re → s ≠ 1 →
      comparisonPrincipalIncompleteL F S η hη P s ≠ 0 := by
  obtain ⟨R, _, ⟨M⟩⟩ := MomentSources.source_exists S η hη P
  exact MomentSources.principal_zero_free_of_selected_source F S η hη P R M

end DedekindZetaZeroFree
