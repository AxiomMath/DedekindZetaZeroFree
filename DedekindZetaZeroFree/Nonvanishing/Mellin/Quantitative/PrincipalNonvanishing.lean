module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.ZeroExclusion
public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalSourceCriterion
public import DedekindZetaZeroFree.Theta.Unfolding.AbsolutelyConvergentExpansion

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative

open DedekindZetaZeroFree

theorem comparisonPrincipalIncompleteL_ne_zero
    (F : Type) [Field F] [NumberField F] (S : SArithmeticData F)
    (η : RayClassCharacter F S.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F S.modulus η) :
    ∀ s : ℂ, 31 / 32 < s.re → s ≠ 1 →
      comparisonPrincipalIncompleteL F S η hη P s ≠ 0 := by
  obtain ⟨R, hR, ⟨M⟩⟩ := DedekindZetaZeroFree.MomentSources.source_exists S η hη P
  intro s hs hs1
  have hzero : R.L s ≠ 0 :=
    RecipeZeroFree.recipe_zero_free (⟨R, hR, M⟩ : FixedData S η) s hs hs1
  exact PrincipalMellin.incomplete_nonzero_of_enlargement F S R.A
    R.containsOriginal R.sameModulus η hη P R.probe.principal R.continuation
    s (by linarith) hs1 hzero

end DedekindZetaZeroFree.Quantitative
