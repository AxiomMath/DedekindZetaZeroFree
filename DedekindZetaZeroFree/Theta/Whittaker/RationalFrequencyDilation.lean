module

public import DedekindZetaZeroFree.Theta.Periods.RationalOrbitFrequencies
public import DedekindZetaZeroFree.Theta.Periods.RationalDiagonalInvariance

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem rationalValue_eq_fourier {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient) (a : Fˣ) (g : Group R) :
    rationalValue R T v a g = fourier R Q.dq (T.theta v)
      (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
        (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a) * g) := by
  let D := KPAdditiveRationalDilation.quotientDilation F a
  let A := KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
    (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)
  let f : KPAdditiveQuotient F → ℂ := fun q => T.theta v
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * (A * g)) *
      star (adelicTraceQuotientCharacter F q : ℂ)
  letI := Q.quotientHaar
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  have hmp := KPAdditiveRationalDilation.quotientDilation_measurePreserving F a Q.dq
  obtain ⟨e, he⟩ := KPAdditiveRationalDilation.quotientDilation_is_additive_homeomorphism F a
  have hme : MeasurableEmbedding D := by
    have hef : (e : _ → _) = D := funext he
    rw [← hef]
    exact e.toHomeomorph.measurableEmbedding
  have htransform (q : KPAdditiveQuotient F) : f (D q) = rationalIntegrand R T v a g q := by
    let x := Quotient.out q
    have hq : (QuotientAddGroup.mk x : KPAdditiveQuotient F) = q := Quotient.out_eq q
    have hd : D q = QuotientAddGroup.mk (algebraMap F (KPAdeles F) (a : F) * x) := by
      rw [← hq]; rfl
    change T.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out (D q)) * (A * g)) *
        star (adelicTraceQuotientCharacter F (D q) : ℂ) = _
    rw [hd]
    have hmk := CompactPeriodAnalyticity.CompactPeriod.cleared_integrand_mk T v 0
      (Metric.mem_ball_self T.radius_pos) (algebraMap F (KPAdeles F) (a : F) * x) (A * g)
    change T.theta v (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (Quotient.out (QuotientAddGroup.mk (algebraMap F (KPAdeles F) (a : F) * x))) * (A * g)) = _ at hmk
    rw [hmk]
    have hchar : adelicTraceQuotientCharacter F
        (QuotientAddGroup.mk (algebraMap F (KPAdeles F) (a : F) * x)) =
        adelicTraceCharacter F (algebraMap F (KPAdeles F) (a : F) * x) :=
      adelicTraceQuotientCharacter_mk F _
    rw [hchar]
    congr 1
    rw [← mul_assoc]
    have hc := KPRationalAdelicSplitting.quotient_upper_diagonal F R.A.zeta12 R.A.primitive_zeta12
      (algebraMap F (KPAdeles F) (a : F) * x)
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)
    change KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (algebraMap F (KPAdeles F) (a : F) * x) * A = A *
        KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
          ((algebraMap F (KPAdeles F) (a : F) * x) * algebraMap F (KPAdeles F) (a⁻¹ : Fˣ)) at hc
    have hx : (algebraMap F (KPAdeles F) (a : F) * x) *
        algebraMap F (KPAdeles F) (a⁻¹ : Fˣ) = x := by
      rw [mul_right_comm, ← map_mul, Units.mul_inv, map_one, one_mul]
    rw [hx] at hc
    rw [hc, mul_assoc]
    change T.theta v (A * (KPGlobalTorusFunctionData.N F R.A.zeta12
      R.A.primitive_zeta12 x * g)) = _
    exact DigitMasks.theta_rational_diagonal R T v a _

  have hi := rationalIntegrand_integrable R T v a g
  have hiD : Integrable (fun q => f (D q)) Q.dq := by
    simpa only [htransform] using hi
  have _hif : Integrable f Q.dq := (hmp.integrable_comp_emb hme).mp hiD
  have h := hmp.integral_comp hme f
  change (∫ q, f (D q) ∂Q.dq) = _ at h
  simpa only [htransform, rationalValue, MomentSources.fourier, f, A] using h

theorem orbitFrequencyValue_eq_fourier {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient)
    (i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A) (g : Group R) :
    orbitFrequencyValue R Q T v i g = fourier R Q.dq (T.theta v)
      (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
        (Units.map (algebraMap F (KPAdeles F)).toMonoidHom ((Quotient.out i.1) * i.2.val)) * g) :=
  rationalValue_eq_fourier R T v ((Quotient.out i.1) * i.2.val) g

end DedekindZetaZeroFree.OrbitFrequencies

end
