module

public import DedekindZetaZeroFree.Theta.Digits.SUnitReindexing

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.ThetaExpansion.QuotientDescent
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem selected_upper_digit_reindex {N : TraceHaarTransport R} (C : JointMellinGaussianSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (u : R.A.U)
    (b : Bool) (y : R.A.G) (d : Digits R m) :
    (Integrable (fun q => C.realization.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) *
        signedArgument R m b (R.A.diagonal (u.val ^ 6) * y) (digitReindex R m u d))) C.sources.dq ∧
     Integrable (fun q => C.realization.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) *
        signedArgument R m b y d)) C.sources.dq) ∧
    upper R C.sources.dq (C.realization.theta v)
      (signedArgument R m b (R.A.diagonal (u.val ^ 6) * y) (digitReindex R m u d)) =
    upper R C.sources.dq (C.realization.theta v) (signedArgument R m b y d) := by
  refine ⟨⟨C.constantTerm.integrable v _, C.constantTerm.integrable v _⟩, ?_⟩
  exact (DedekindZetaZeroFree.DigitMasks.signed_term_reindex R C.realization v m u b y d).2
end DedekindZetaZeroFree.ThetaExpansion.QuotientDescent

end
