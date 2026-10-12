module

public import DedekindZetaZeroFree.Theta.Digits.FiniteCharacterMasks
public import DedekindZetaZeroFree.Eisenstein.Induction.RationalBorelCovariance

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources NumberField MeasureTheory
open scoped Classical BigOperators
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem rationalLift_mk (g : Matrix.GeneralLinearGroup (Fin 2) F) :
    KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12
      (Matrix.ProjGenLinGroup.mk g) =
      KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.rationalHom F R.A.zeta12 R.A.primitive_zeta12 g) := by
  rw [KPLiteralExceptionalResidue.rationalLift_eq_constructed]
  exact (KPGlobalResidualConstruction.ElementaryOutputs.rationalSplitting
    F R.A.zeta12 R.A.primitive_zeta12).on_matrix g

end DedekindZetaZeroFree.DigitMasks

end
