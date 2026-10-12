module

public import DedekindZetaZeroFree.Theta.Digits.FiniteCharacterMasks
public import DedekindZetaZeroFree.Theta.Digits.NormLevelQuotientDescent

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources NumberField
open scoped Classical BigOperators
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem residueSixthUnit_is_sixth (p : ThetaBranch.ExteriorPrime R.A) (u : R.A.U) :
    ∃ z : (ThetaDigitAverage.Residue p.val)ˣ,
      ThetaDigitDescent.residueSixthUnit R.A p.val p.property u = z ^ 6 := by
  refine ⟨Units.map (ThetaDigitDescent.residueComparison R.A p.val p.property).symm.toRingHom.toMonoidHom
    (Units.map (Ideal.Quotient.mk _).toMonoidHom (R.A.unitEquiv u)), ?_⟩
  simp only [ThetaDigitDescent.residueSixthUnit, map_pow]

theorem mask_residueSixthUnit (p : ThetaBranch.ExteriorPrime R.A) (u : R.A.U)
    (j : Fin 6) (d : DHCubic.Residue F p.val) :
    sexticFourierMask (ThetaBranch.residueCharacter R.A R.σ p) (Characters.psi R p) j
      (ThetaDigitDescent.residueSixthUnit R.A p.val p.property u * d) =
    sexticFourierMask (ThetaBranch.residueCharacter R.A R.σ p) (Characters.psi R p) j d := by
  obtain ⟨z, hz⟩ := residueSixthUnit_is_sixth R p u
  rw [hz, Units.val_pow_eq_pow_val]
  exact mask_mul_sixth _ _ (character_order R p) z j d

def digitReindex (m : ThetaReflectionData.Row R.A) (u : R.A.U) :
    ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property) ≃
      ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property) :=
  ThetaDigitDescent.reindex R.A _
    (fun p hp => ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp hp).1) u

theorem digitWeight_reindex (m : ThetaReflectionData.Row R.A) (u : R.A.U)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    digitWeight R m (digitReindex R m u d) = digitWeight R m d := by
  unfold digitWeight
  apply Finset.prod_congr rfl
  intro p _
  exact mask_residueSixthUnit R ⟨p.val,
    ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1⟩
    u (ThetaDigitAverage.rowExponent R.A m.val p.val) (d p)

end DedekindZetaZeroFree.DigitMasks

end
