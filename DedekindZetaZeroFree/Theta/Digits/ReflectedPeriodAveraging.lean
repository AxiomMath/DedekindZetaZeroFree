module

public import DedekindZetaZeroFree.Theta.Unfolding.ReflectedEvaluationFromExtraction

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem reverse_digit_period {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (i : OrbitIndex R) (y : R.A.G)
    (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    Integrable (orbitFrequencyIntegrand R C.sources C.realization v i
      (signedArgument R m false y d)) C.sources.dq ∧
    orbitFrequencyValue R C.sources C.realization v i (signedArgument R m false y d) =
      fourier R C.sources.dq (C.realization.theta v)
        (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
          (Units.map (algebraMap F (KPAdeles F)).toMonoidHom ((Quotient.out i.1) * i.2.val)) *
          (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * diagonal R y *
            KPRationalAdelicSplitting.pglN F R.A.zeta12 R.A.primitive_zeta12 (digitParameter R m d))) := by
  refine ⟨C.absolute.orbit_period_integrable v i _, ?_⟩
  rw [orbitFrequencyValue_eq_fourier]
  rfl

theorem orbitSheet_reverse_period_word {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (i : OrbitIndex R) (l : PositiveAxis) (z : Sheet R.A l) :
    orbitSheet R C v m false i l z =
      (if QuotientGroup.mk' R.A.sixthPowers z.val ∈ R.probe.correction.B then 1 else 0) *
        (C.packet.branch v z.val)⁻¹ *
        ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
          digitWeight R m d * fourier R C.sources.dq (C.realization.theta v)
            (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
              (Units.map (algebraMap F (KPAdeles F)).toMonoidHom ((Quotient.out i.1) * i.2.val)) *
              (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * diagonal R z.val *
                KPRationalAdelicSplitting.pglN F R.A.zeta12 R.A.primitive_zeta12 (digitParameter R m d))) := by
  unfold orbitSheet
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  rw [(reverse_digit_period R C v i z.val m d).2]

end DedekindZetaZeroFree.OrbitExpansion

end
