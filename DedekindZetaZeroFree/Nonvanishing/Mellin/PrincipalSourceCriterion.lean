module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SixthRootAlignment
public import DedekindZetaZeroFree.Nonvanishing.Mellin.ProbeInversion

@[expose] public section

namespace DedekindZetaZeroFree.MomentSources

theorem principal_zero_free_of_selected_source
    (F : Type) [Field F] [NumberField F]
    (S : SArithmeticData F) (η : RayClassCharacter F S.modulus)
    (hη : η.IsPrincipal) (P : PrincipalRayHeckeData F S.modulus η)
    (R : PrincipalMellin.ActualRecipe S η) (M : SelectedMomentSource R) :
    ∀ s : ℂ, (5999 / 6000 : ℝ) < s.re → s ≠ 1 →
      comparisonPrincipalIncompleteL F S η hη P s ≠ 0 := by
  have hzero := recipe_zero_free_of_moment R (moment_of_source R M)
  intro s hs hs1
  exact PrincipalMellin.incomplete_nonzero_of_enlargement F S R.A
    R.containsOriginal R.sameModulus η hη P R.probe.principal R.continuation
    s (by linarith) hs1 (hzero s hs hs1)

end DedekindZetaZeroFree.MomentSources
