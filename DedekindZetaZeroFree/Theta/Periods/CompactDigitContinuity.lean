module

public import DedekindZetaZeroFree.Theta.Periods.WeightedQuotientIntegrability

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem theta_upper_integrable {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (g : Group R) :
    Integrable (fun q : KPAdditiveQuotient F => T.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) Q.dq :=
  CompactPeriodAnalyticity.CompactPeriod.cleared_integrable T v 0 (Metric.mem_ball_self T.radius_pos) g

theorem theta_upper_joint_continuous {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) :
    Continuous (fun p : Group R × KPAdditiveQuotient F => T.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out p.2) * p.1)) := by
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  apply ((IsOpenQuotientMap.id (X := Group R)).prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk
      (N := AdeleRing.principalSubgroup (𝓞 F) F))).continuous_comp_iff.mp
  have hc : Continuous (fun p : Group R × KPAdeles F => T.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 p.2 * p.1)) :=
    (T.smooth v 0 (Metric.mem_ball_self T.radius_pos)).1.comp
      (((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
        F R.A.zeta12 R.A.primitive_zeta12).comp continuous_snd).mul continuous_fst)
  simpa only [Function.comp_def, Prod.map, id_eq, Realization.theta,
    CompactPeriodAnalyticity.CompactPeriod.cleared_integrand_mk T v 0 (Metric.mem_ball_self T.radius_pos),
    Pi.mul_apply] using hc

theorem upper_continuous {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) : Continuous (upper R Q.dq (T.theta v)) := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  have hi := theta_upper_integrable R T v
  apply continuousOn_univ.mp
  exact continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
    (theta_upper_joint_continuous R T v).continuousOn (by simp)

theorem upperDigits_continuous {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool) :
    Continuous (upperDigits R Q T v m b) := by
  apply continuous_finset_sum
  intro d _
  exact continuous_const.mul ((upper_continuous R T v).comp (signedArgument_continuous R m b d))

end DedekindZetaZeroFree.DigitMasks

end
