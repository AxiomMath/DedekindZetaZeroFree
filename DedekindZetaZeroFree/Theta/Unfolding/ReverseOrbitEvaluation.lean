module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.GammaInvariantCoefficients

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem orbitSheet_reverse_extraction {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (ξ : ThetaReflectionData.Frequency R.A) (γ : ThetaReflectionData.rationalGamma R.A)
    (l : PositiveAxis) (y : Sheet R.A l) :
    orbitSheet R C v m false (ξ, γ) l y =
      exteriorDigitCoefficient R C m (Quotient.out ξ) *
        reverseSheetWord R C.realization C.packet v (Quotient.out ξ) γ y.val := by
  rw [orbitSheet_reverse_period_word]
  have hword (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
      KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
        (Units.map (algebraMap F (KPAdeles F)).toMonoidHom (Quotient.out ξ * γ.val)) *
        (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * diagonal R y.val *
          KPRationalAdelicSplitting.pglN F R.A.zeta12 R.A.primitive_zeta12 (digitParameter R m d)) =
      restrictedLift R (reverseTuple R (γ.val * Quotient.out ξ) y.val m d) := by
    rw [mul_comm (Quotient.out ξ) γ.val]
    rfl
  simp_rw [hword, reverse_digit_extracted]
  simp only [← mul_assoc, ← Finset.sum_mul]
  change (_ * _ * exteriorDigitCoefficient R C m (γ.val * Quotient.out ξ)) * _ * _ = _
  rw [exteriorDigitCoefficient_gamma]
  unfold reverseSheetWord
  ring

theorem reverse_orbit_evaluation_clean {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun ξ => ‖actualReflectedTerm R C v m Z ξ‖) ∧
    HasSum (actualReflectedTerm R C v m Z)
      (∑' i : OrbitIndex R, orbitTerm R C v m false Z hZ i) := by
  apply reverse_orbit_evaluation_of_pointwise_extraction R C hx v m Z hZ
  intro ξ γ l
  filter_upwards [] with y
  exact orbitSheet_reverse_extraction R C v m ξ γ l y

end DedekindZetaZeroFree.OrbitExpansion

end
