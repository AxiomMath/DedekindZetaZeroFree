module

public import DedekindZetaZeroFree.Metaplectic.Torus.DiagonalFourierPhases

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

 theorem localIdele_one : localIdele R (1 : R.A.G) = 1 := by
  simp [MomentSources.localIdele, KPRationalAdelicSplitting.localIdele]

 theorem localIdele_inv (y : R.A.G) : localIdele R y⁻¹ = (localIdele R y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← IdeleInsertion.localIdele_mul, inv_mul_cancel, localIdele_one]

 theorem globalWeyl_diagonal (y : R.A.G) :
    KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * diagonal R y =
      diagonal R y⁻¹ * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 := by
  unfold MomentSources.diagonal
  rw [localIdele_inv, KPRationalAdelicSplitting.quotient_weyl_diagonal]

theorem reverse_s_period {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (x : Fˣ) (y : R.A.G) :
    fourier R C.sources.dq (C.realization.theta v)
      (diagonal R (R.A.diagonal x) * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * diagonal R y) =
    (R.σ ((R.probe.correction.H
      (QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal x))
      (QuotientGroup.mk' R.A.sixthPowers y⁻¹) : Fˣ) : F) ^ 2)⁻¹ *
      fourier R C.sources.dq (C.realization.theta v)
        (diagonal R (R.A.diagonal x / y) * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12) := by
  rw [mul_assoc, globalWeyl_diagonal, ← mul_assoc, fourier_diagonal_mul]
  rw [correction_pairing_eq, R.A.H_S6_on_representatives]
  rfl

theorem reverse_digit_extracted {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (x : Fˣ) (y : R.A.G) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    fourier R C.sources.dq (C.realization.theta v) (restrictedLift R (reverseTuple R x y m d)) =
      (∏ᶠ p : ThetaBranch.ExteriorPrime R.A, ThetaExpansion.SignedExpansion.exteriorDigitFactor R C m x d p) *
      (R.σ ((R.probe.correction.H
        (QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal x))
        (QuotientGroup.mk' R.A.sixthPowers y⁻¹) : Fˣ) : F) ^ 2)⁻¹ *
      fourier R C.sources.dq (C.realization.theta v)
        (diagonal R (R.A.diagonal x / y) * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12) := by
  rw [(reverseTuple_period R C v x y m d).2, sReverseTuple_period, reverse_s_period, mul_assoc]

end DedekindZetaZeroFree.OrbitExpansion

end
