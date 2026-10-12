module

public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.OrbitContinuity
public import DedekindZetaZeroFree.Theta.Periods.RestrictedTensorIntegration

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open ThetaExpansion MomentSources KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 150000

open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12

open CurrentOutputExtension
local instance completedPeriodCoreAdd : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance completedPeriodCoreModule : Module ℂ complexCore := Submodule.module complexCore
local instance completedPeriodCoreTopology : TopologicalSpace complexCore := instTopologicalSpaceSubtype
local instance completedPeriodPrincipalUniform : IsUniformAddGroup (PrincipalSeries negativeParameter) :=
  isUniformAddGroup_of_addCommGroup
local instance completedPeriodCoreUniform : IsUniformAddGroup complexCore :=
  complexCore.toAddSubgroup.isUniformAddGroup

variable (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
variable (x : ∀j : s.val,LiteralSource.Plus R.A P C j.val)
variable (w : InfinitePlace F) (hw : Sum.inl w∈s.val)
variable (g : MomentSources.Group R)
local notation "slot" => restrictedSlotTensor R.A P C s x w hw

local notation "dq" => KPWildKernelUpperBound.quotientHaar F

def originalFourierMap : C(KPAdditiveQuotient F,ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫q,f q*star (adelicTraceQuotientCharacter F q : ℂ) ∂dq
  map_add' f h := by
    have hi (f : C(KPAdditiveQuotient F,ℂ)) :
        Integrable (fun q=>f q*star (adelicTraceQuotientCharacter F q : ℂ)) dq :=
      (f.continuous.mul trace_weight_continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    simp only [ContinuousMap.add_apply,add_mul]
    exact integral_add (hi f) (hi h)
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply,smul_eq_mul,mul_assoc]
    exact integral_const_mul c _

theorem originalFourierMap_bound (f : C(KPAdditiveQuotient F,ℂ)) :
    ‖originalFourierMap (F:=F) f‖ ≤ ‖f‖ := by
  have hb : ∀ᵐq ∂dq,‖f q*star (adelicTraceQuotientCharacter F q : ℂ)‖≤‖f‖ := by
    filter_upwards [] with q
    rw [norm_mul,norm_star,Circle.norm_coe,mul_one]
    exact f.norm_coe_le_norm q
  simpa only [originalFourierMap,LinearMap.coe_mk,AddHom.coe_mk,Measure.real,
    measure_univ,ENNReal.toReal_one,mul_one] using
      norm_integral_le_of_norm_le_const (α:=KPAdditiveQuotient F) (μ:=dq)
        (f:=fun q:KPAdditiveQuotient F=>f q*star (adelicTraceQuotientCharacter F q : ℂ)) hb

def originalFourierCLM : C(KPAdditiveQuotient F,ℂ) →L[ℂ] ℂ :=
  (originalFourierMap (F:=F)).mkContinuous 1 (fun f=>by simpa using originalFourierMap_bound f)

def completedPeriod : PrincipalSeries negativeParameter →L[ℂ] ℂ :=
  originalFourierCLM.comp (completedObservation R N P C  s x w hw g)

theorem completedPeriod_core (v : complexCore) :
    completedPeriod R N P C  s x w hw g (smoothInclusion v)=
      restrictedSlotPeriod R P C s x w hw g v := by
  change originalFourierCLM (completedObservation R N P C  s x w hw g (smoothInclusion v))=_
  rw [completedObservation_core]
  rfl

theorem completedPeriod_integral (v : PrincipalSeries negativeParameter) :
    completedPeriod R N P C  s x w hw g v=
      ∫q:KPAdditiveQuotient F,
        canonicalOutput R N P C  s x w hw
          (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*g) v*
          star (adelicTraceQuotientCharacter F q : ℂ) ∂dq := by
  change (∫q:KPAdditiveQuotient F,
    completedObservation R N P C  s x w hw g v q*
      star (adelicTraceQuotientCharacter F q : ℂ) ∂dq)=_
  apply integral_congr_ae
  filter_upwards [] with q
  rw [completedObservation_eq_output]

theorem corePeriod_left_root (z : RestrictedTensorSimple.Core (LiteralSource.Plus R.A P C)
    (LiteralSource.plusReference R.A P C) (LiteralSource.bad R.A P C)) (a : KPAdeles F) :
    corePeriod R P C (KPGlobalTorusFunctionData.N F ζ hζ a*g) z=
      (adelicTraceQuotientCharacter F (QuotientAddGroup.mk a):ℂ)*corePeriod R P C g z := by
  apply ExteriorWhittakerValues.StoredWhittaker.fourier_left_root R dq _ ?_ a g
    (core_period_integrable R P C z g)
  intro t g
  rw [←KPLiteralExceptionalResidue.rationalLift_unipotent]
  exact (LiteralSource.coreResidue_raw_automorphic R P C z).2.1 _ _

theorem completedPeriod_left_root (a : KPAdeles F) (v : PrincipalSeries negativeParameter) :
    completedPeriod R N P C  s x w hw
      (KPGlobalTorusFunctionData.N F ζ hζ a*g) v=
      (adelicTraceQuotientCharacter F (QuotientAddGroup.mk a):ℂ)*
        completedPeriod R N P C  s x w hw g v := by
  refine smoothInclusion_denseRange.induction_on v ?_ ?_
  · exact isClosed_eq (completedPeriod R N P C  s x w hw _).continuous
      (continuous_const.mul (completedPeriod R N P C  s x w hw g).continuous)
  · intro u
    rw [completedPeriod_core,completedPeriod_core]
    exact corePeriod_left_root R P C g (slot u) a
end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
