module

public import DedekindZetaZeroFree.Theta.Profiles.IdelicDilation
public import DedekindZetaZeroFree.Eisenstein.Induction.RationalInvariance
public import DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.CompactPeriod
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
variable {Q : AdmissibleFlatSources R}

theorem cleared_rational (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius)
    (γ : Matrix.ProjGenLinGroup (Fin 2) F) (g : Group R) :
    T.cleared v s (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) =
      T.cleared v s g := by
  let a := KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g
  have hopen : IsOpen {z : ℂ | (1 : ℝ) / 3 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h1 : (1 : ℂ) ∈ {z : ℂ | (1 : ℝ) / 3 < z.re} := by norm_num
  have hnear : (fun z => T.E v z a) =ᶠ[𝓝[≠] (1 : ℂ)] (fun z => T.E v z g) := by
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds h1)] with z hz
    rw [T.chamber v z hz a, T.chamber v z hz g]
    exact KPLiteralExceptionalResidue.ResidueAutomorphy.eisenstein_rational
      F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) z hz γ g
  have htop : meromorphicOrderAt (fun z => T.E v z a - T.E v z g) 1 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [hnear] with z hz
    exact sub_eq_zero.mpr hz
  have hz : (0 : ℂ) ∈ Metric.ball (0 : ℂ) T.radius := Metric.mem_ball_self T.radius_pos
  have htop0 := ((T.meromorphic v a).sub (T.meromorphic v g)).meromorphicOrderAt_eq_top_of_isPreconnected
    KPContinuation.spectralDomain_isConnected.isPreconnected
    (KPContinuation.convergenceHalfPlane_subset_spectralDomain h1) (T.disc_domain hz) htop
  have hcleared : (fun z => T.cleared v z a) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => T.cleared v z g) := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp htop0,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) T.radius_pos), self_mem_nhdsWithin]
      with z he hz hz0
    have ha := congrFun (T.clears v z hz hz0) a
    have hb := congrFun (T.clears v z hz hz0) g
    simp only [Pi.smul_apply, smul_eq_mul] at ha hb
    change T.E v z a - T.E v z g = 0 at he
    rw [ha, hb, sub_eq_zero.mp he]
  have ha := T.analytic v a
  have hb := T.analytic v g
  have he := ((ha 0 hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hb 0 hz).continuousAt).mp hcleared
  exact ha.eqOn_of_preconnected_of_eventuallyEq hb (convex_ball (0 : ℂ) T.radius).isPreconnected
    hz he hs

theorem cleared_integrand_mk (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius) (x : KPAdeles F) (g : Group R) :
    T.cleared v s (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (Quotient.out (QuotientAddGroup.mk x : KPAdditiveQuotient F)) * g) =
    T.cleared v s (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add
    (AdeleRing.principalSubgroup (𝓞 F) F) x
  obtain ⟨t, ht⟩ := r.property
  rw [hr, ← ht, add_comm, KPGlobalTorusFunctionData.N_add, mul_assoc,
    ← KPLiteralExceptionalResidue.rationalLift_unipotent]
  exact cleared_rational T v s hs _ _

theorem cleared_integrand_continuous (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius) (g : Group R) :
    Continuous (fun q : KPAdditiveQuotient F => T.cleared v s
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) := by
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  apply (QuotientAddGroup.isQuotientMap_mk
    (AdeleRing.principalSubgroup (𝓞 F) F)).continuous_iff.mpr
  simpa only [Function.comp_def, cleared_integrand_mk T v s hs, Pi.mul_apply] using
    (T.smooth v s hs).1.comp
      ((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
        F R.A.zeta12 R.A.primitive_zeta12).mul continuous_const)

theorem cleared_integrable (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius) (g : Group R) :
    Integrable (fun q : KPAdditiveQuotient F => T.cleared v s
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) Q.dq := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  simpa using (cleared_integrand_continuous T v s hs g).continuousOn.integrableOn_compact'
    isCompact_univ MeasurableSet.univ

end DedekindZetaZeroFree.CompactPeriodAnalyticity.CompactPeriod

end
