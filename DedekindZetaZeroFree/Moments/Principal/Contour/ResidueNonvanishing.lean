module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.SpectralFunction

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.ResidueNonzero

noncomputable section

variable {F : Type} [Field F] [NumberField F]
variable {S : DedekindZetaZeroFree.SArithmeticData F}
variable {η : DedekindZetaZeroFree.RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem RS_ne_zero : Spectral.RS D ≠ 0 := by
  unfold Spectral.RS DedekindZetaZeroFree.comparisonPrincipalResidue
  apply mul_ne_zero
  · exact DedekindZetaZeroFree.PrincipalMellinComparison.principal_regularization_ne_zero F
      D.recipe.A.modulus D.recipe.A.modulus_ne_zero D.recipe.target D.recipe.probe.principal
      D.recipe.continuation
  · exact DedekindZetaZeroFree.MellinZeroFree.comparisonPrincipalIncompleteL_eulerFactors_ne_zero
      F D.recipe.A D.recipe.target 1 (by norm_num)

theorem c₀_ne_zero : Spectral.c₀ D ≠ 0 := by
  unfold Spectral.c₀
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (RS_ne_zero D)) D.M_one_sixth_ne_zero)
      D.W1Hat_one_ne_zero) (by norm_num)

end

end DedekindZetaZeroFree.Quantitative.ResidueNonzero
