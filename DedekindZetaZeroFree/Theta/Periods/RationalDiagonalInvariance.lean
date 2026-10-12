module

public import DedekindZetaZeroFree.Theta.Periods.WeylInvariantAverages
public import DedekindZetaZeroFree.Theta.Periods.ExteriorSphericalInvariance
public import DedekindZetaZeroFree.Theta.Digits.NormLevelQuotientDescent

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
open _root_.DedekindZetaZeroFree.ThetaDigitDescent renaming scale → scale
open _root_.DedekindZetaZeroFree.ThetaDigitDescent renaming scale_mk → scale_mk
open _root_.DedekindZetaZeroFree.ThetaDigitDescent renaming scale_continuous → scale_continuous
open _root_.DedekindZetaZeroFree.ThetaDigitDescent renaming scale_inverse → scale_inverse
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem pglA_rational (a : Fˣ) :
    KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a) =
    KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12
      (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d F a 1)) := by
  rw [rationalLift_mk]
  unfold KPRationalAdelicSplitting.pglA
  exact congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12)
    (KPRationalAdelicSplitting.A_rational F R.A.zeta12 R.A.primitive_zeta12 a)

theorem theta_rational_diagonal {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (a : Fˣ) (g : Group R) :
    T.theta v (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a) * g) = T.theta v g := by
  rw [pglA_rational R]
  exact (T.automorphic v).2.1 _ g

theorem upper_rational_diagonal {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (a : Fˣ) (g : Group R) :
    upper R Q.dq (T.theta v)
      (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
        (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a) * g) =
      upper R Q.dq (T.theta v) g := by
  letI : Q.dq.IsAddHaarMeasure := Q.quotientHaar
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  let D := scale (F := F) (a : F)
  have hc : Continuous D := scale_continuous _
  have hsurj : Function.Surjective D := by
    intro z
    exact ⟨scale (F := F) (a⁻¹ : Fˣ) z, scale_inverse a⁻¹ z⟩
  have hinj : Function.Injective D := Function.LeftInverse.injective (scale_inverse a)
  have hmp : MeasurePreserving D Q.dq Q.dq := D.measurePreserving hc hsurj rfl
  let A := KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
    (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)
  let f := fun q : KPAdditiveQuotient F => T.theta v
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * (A * g))
  have hint : Integrable f Q.dq := theta_upper_integrable R T v (A * g)
  have htrans (q : KPAdditiveQuotient F) : f (D q) = T.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp only [f, D, scale_mk, Realization.theta,
      CompactPeriodAnalyticity.CompactPeriod.cleared_integrand_mk T v 0 (Metric.mem_ball_self T.radius_pos)]
    change T.theta v (KPRationalAdelicSplitting.pglN F R.A.zeta12 R.A.primitive_zeta12
      (algebraMap F (KPAdeles F) (a : F) * x) * (A * g)) = _
    rw [← mul_assoc, KPRationalAdelicSplitting.quotient_upper_diagonal, mul_assoc]
    have he : (algebraMap F (KPAdeles F) (a : F) * x) *
        (((Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)⁻¹ : (KPAdeles F)ˣ) : KPAdeles F) = x := by
      change (algebraMap F (KPAdeles F) (a : F) * x) *
        algebraMap F (KPAdeles F) ((a⁻¹ : Fˣ) : F) = x
      rw [mul_right_comm, ← map_mul, Units.mul_inv, map_one, one_mul]
    rw [he, theta_rational_diagonal R T]
    rfl
  have hi := (hc.isClosedEmbedding hinj).integral_map (μ := Q.dq) f
  rw [hmp.map_eq] at hi
  simp_rw [htrans] at hi
  exact hi

end DedekindZetaZeroFree.DigitMasks

end
