module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CompactPeriod.JointContinuity
public import DedekindZetaZeroFree.Theta.Unfolding.FactorizationAndMellinNormalizationData

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
variable {Q : AdmissibleFlatSources R}

theorem theta_orbit_continuous (T : Realization R Q) (v : R.A.UnitQuotient)
    (g : Group R) :
    Continuous (fun q : KPAdditiveQuotient F => T.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) :=
  CompactPeriodAnalyticity.CompactPeriod.cleared_integrand_continuous T v 0
    (Metric.mem_ball_self T.radius_pos) g

theorem trace_weight_continuous :
    Continuous (fun q : KPAdditiveQuotient F =>
      star (adelicTraceQuotientCharacter F q : ℂ)) :=
  continuous_star.comp (continuous_subtype_val.comp (continuous_adelicTraceQuotientCharacter F))

theorem theta_period_integrable (T : Realization R Q) (v : R.A.UnitQuotient)
    (g : Group R) :
    Integrable (fun q : KPAdditiveQuotient F => T.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  exact ((theta_orbit_continuous T v g).mul trace_weight_continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem sameResidue_orbit_continuous (T : Realization R Q) {f : Functions R}
    (hf : f ∈ sameResidueModule T) (g : Group R) :
    Continuous (fun q : KPAdditiveQuotient F => f
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) := by
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover
      F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  apply (QuotientAddGroup.isOpenQuotientMap_mk
    (N := AdeleRing.principalSubgroup (𝓞 F) F)).continuous_comp_iff.mp
  convert hf.2.1.comp
    ((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
      F R.A.zeta12 R.A.primitive_zeta12).mul (continuous_const (y := g))) using 1
  funext a
  obtain ⟨r, he⟩ := QuotientAddGroup.mk_out_eq_add
    (AdeleRing.principalSubgroup (𝓞 F) F) a
  obtain ⟨t, ht⟩ := r.property
  change f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
    (Quotient.out (QuotientAddGroup.mk a : KPAdditiveQuotient F)) * g) = _
  rw [he, ← ht, add_comm, KPGlobalTorusFunctionData.N_add, mul_assoc,
    ← KPLiteralExceptionalResidue.rationalLift_unipotent, hf.2.2.1]
  rfl

theorem sameResidue_period_integrable (T : Realization R Q) {f : Functions R}
    (hf : f ∈ sameResidueModule T) (g : Group R) :
    Integrable (fun q : KPAdditiveQuotient F => f
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  exact ((sameResidue_orbit_continuous T hf g).mul trace_weight_continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end DedekindZetaZeroFree.FourierContinuation

end

section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
variable {Q : AdmissibleFlatSources R}

def translateSpan (T : Realization R Q) : Submodule ℂ (Functions R) :=
  Submodule.span ℂ {f : Functions R | ∃ v a,
    f = KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a (T.theta v)}

theorem translateSpan_orbit_continuous (T : Realization R Q) {f : Functions R}
    (hf : f ∈ translateSpan T) (g : Group R) :
    Continuous (fun q : KPAdditiveQuotient F => f
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v, a, rfl⟩ := hf
    change Continuous (fun q : KPAdditiveQuotient F => T.theta v
      ((KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) * a))
    simpa only [mul_assoc] using theta_orbit_continuous T v (g * a)
  | zero => exact continuous_const
  | add f h _ _ hf hh => exact hf.add hh
  | smul c f _ hf => exact continuous_const.smul hf

theorem translateSpan_period_integrable (T : Realization R Q) {f : Functions R}
    (hf : f ∈ translateSpan T) (g : Group R) :
    Integrable (fun q : KPAdditiveQuotient F => f
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  exact ((translateSpan_orbit_continuous T hf g).mul trace_weight_continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def orbit (T : Realization R Q) (g : Group R) :
    translateSpan T →ₗ[ℂ] C(KPAdditiveQuotient F, ℂ) where
  toFun f := ⟨fun q => f.val
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g),
    translateSpan_orbit_continuous T f.property g⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def period (T : Realization R Q) (g : Group R) : translateSpan T →ₗ[ℂ] ℂ where
  toFun f := MomentSources.fourier R Q.dq f.val g
  map_add' f h := by
    unfold MomentSources.fourier
    simp only [Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (translateSpan_period_integrable T f.property g)
      (translateSpan_period_integrable T h.property g)
  map_smul' c f := by
    unfold MomentSources.fourier
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact integral_const_mul c _

theorem cleared_period_integrable (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius) (g : Group R) :
    Integrable (fun q : KPAdditiveQuotient F => T.cleared v s
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  exact ((CompactPeriodAnalyticity.CompactPeriod.cleared_integrand_continuous T v s hs g).mul
    trace_weight_continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem fourier_cleared_continuousOn (T : Realization R Q) (v : R.A.UnitQuotient)
    (g : Group R) :
    ContinuousOn (fun s => MomentSources.fourier R Q.dq (T.cleared v s) g)
      (Metric.ball (0 : ℂ) T.radius) := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun s : Metric.ball (0 : ℂ) T.radius => ∫ q : KPAdditiveQuotient F,
    T.cleared v s.val
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ) ∂Q.dq)
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
  · exact ((CompactPeriodAnalyticity.CompactPeriod.cleared_quotient_joint_continuous T v g).mul
      (trace_weight_continuous.comp continuous_snd)).continuousOn
  · intro p q hp hq
    exact False.elim (hq (Set.mem_univ q))

theorem fourier_cleared_tendsto_zero (T : Realization R Q) (v : R.A.UnitQuotient)
    (g : Group R) :
    Filter.Tendsto (fun s => MomentSources.fourier R Q.dq (T.cleared v s) g) (nhds (0 : ℂ))
      (nhds (MomentSources.fourier R Q.dq (T.theta v) g)) :=
  ((fourier_cleared_continuousOn T v g 0 (Metric.mem_ball_self T.radius_pos)).continuousAt
    (Metric.ball_mem_nhds (0 : ℂ) T.radius_pos))

def sameResidueOrbit (T : Realization R Q) (g : Group R) :
    sameResidueModule T →ₗ[ℂ] C(KPAdditiveQuotient F, ℂ) where
  toFun f := ⟨fun q => f.val
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g),
    sameResidue_orbit_continuous T f.property g⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

end DedekindZetaZeroFree.FourierContinuation

end
end
