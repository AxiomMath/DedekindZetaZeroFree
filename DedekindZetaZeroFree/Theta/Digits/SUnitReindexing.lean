module

public import DedekindZetaZeroFree.Theta.Digits.ThetaAndUpperPeriodDescent
public import DedekindZetaZeroFree.Theta.Digits.TracePhasesAndMaskInversion

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField
namespace DedekindZetaZeroFree.ThetaExpansion.QuotientDescent
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def digitReindex (m : ThetaReflectionData.Row R.A) (u : R.A.U) : Digits R m ≃ Digits R m :=
  ThetaDigitDescent.reindex R.A (ThetaDigitAverage.rowPrimes R.A m.val m.property)
    (fun p hp => ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp hp).1) u

open _root_.DedekindZetaZeroFree.ThetaDigitDescent renaming sexticFourierMask_mul_eq → sexticFourierMask_mul_eq
open _root_.DedekindZetaZeroFree.ThetaDigitDescent renaming chi_sixth_pow_eq_one → chi_sixth_pow_eq_one

theorem digitWeight_reindex (m : ThetaReflectionData.Row R.A) (u : R.A.U) (d : Digits R m) :
    digitWeight R m (digitReindex R m u d) = digitWeight R m d := by
  unfold digitWeight
  apply Finset.prod_congr rfl
  intro p _
  let hp := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
  let z : (ThetaDigitAverage.Residue p.val)ˣ :=
    Units.map (ThetaDigitDescent.residueComparison R.A p.val hp).symm.toRingHom.toMonoidHom
      (Units.map (Ideal.Quotient.mk _).toMonoidHom (R.A.unitEquiv u))
  have hz : ThetaDigitDescent.residueSixthUnit R.A p.val hp u = z ^ 6 := by
    simp only [ThetaDigitDescent.residueSixthUnit, z, map_pow]
  have ho : orderOf (ThetaBranch.residueCharacter R.A R.σ ⟨p.val, hp⟩) = 6 :=
    DHCubic.orderOf_normalizedSextic_complex F R.A p.val hp R.σ _
      (DHCubic.existsUnique_normalizedSextic F R.A p.val hp).exists.choose_spec
  have hchi : ThetaBranch.residueCharacter R.A R.σ ⟨p.val, hp⟩
      (ThetaDigitDescent.residueSixthUnit R.A p.val hp u) = 1 := by
    rw [hz, Units.val_pow_eq_pow_val]
    exact chi_sixth_pow_eq_one _ ho z.ne_zero
  change sexticFourierMask _ _ _
    ((ThetaDigitDescent.residueSixthUnit R.A p.val hp u : ThetaDigitAverage.Residue p.val) * d p) = _
  exact sexticFourierMask_mul_eq _ _ ho hchi _ _

theorem selected_theta_digit_reindex {N : TraceHaarTransport R} (C : JointMellinGaussianSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (u : R.A.U)
    (b : Bool) (y : R.A.G) (d : Digits R m) :
    C.realization.theta v (signedArgument R m b (R.A.diagonal (u.val ^ 6) * y)
      (digitReindex R m u d)) =
    C.realization.theta v (signedArgument R m b y d) := by
  exact (DedekindZetaZeroFree.DigitMasks.signed_term_reindex R C.realization v m u b y d).1
end DedekindZetaZeroFree.ThetaExpansion.QuotientDescent

end
