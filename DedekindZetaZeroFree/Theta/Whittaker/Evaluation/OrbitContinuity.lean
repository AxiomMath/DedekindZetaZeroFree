module

public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.CanonicalExtension
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.OrbitBounds

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
local instance observationCoreAdd : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance observationCoreModule : Module ℂ complexCore := Submodule.module complexCore
local instance observationCoreTopology : TopologicalSpace complexCore := instTopologicalSpaceSubtype
local instance observationPrincipalUniform : IsUniformAddGroup (PrincipalSeries negativeParameter) :=
  isUniformAddGroup_of_addCommGroup
local instance observationCoreUniform : IsUniformAddGroup complexCore :=
  complexCore.toAddSubgroup.isUniformAddGroup

variable (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
variable (x : ∀j : s.val,LiteralSource.Plus R.A P C j.val)
variable (w : InfinitePlace F) (hw : Sum.inl w∈s.val)
variable (g : MomentSources.Group R)
local notation "slot" => restrictedSlotTensor R.A P C s x w hw

theorem slot_orbit_continuous (v : complexCore) :
    Continuous (fun q:KPAdditiveQuotient F => LiteralSource.coreResidue R P C (slot v)
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*g)) := by
  letI : IsTopologicalGroup (MomentSources.Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hf := LiteralSource.coreResidue_raw_automorphic R P C (slot v)
  apply (QuotientAddGroup.isOpenQuotientMap_mk
    (N:=AdeleRing.principalSubgroup (𝓞 F) F)).continuous_comp_iff.mp
  convert hf.1.1.comp
    ((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous F ζ hζ).mul
      (continuous_const (y:=g))) using 1
  funext a
  obtain ⟨r,he⟩ := QuotientAddGroup.mk_out_eq_add (AdeleRing.principalSubgroup (𝓞 F) F) a
  obtain ⟨t,ht⟩ := r.property
  change LiteralSource.coreResidue R P C (slot v)
    (KPGlobalTorusFunctionData.N F ζ hζ
      (Quotient.out (QuotientAddGroup.mk a : KPAdditiveQuotient F))*g) = _
  rw [he,←ht,add_comm,KPGlobalTorusFunctionData.N_add,mul_assoc,
    ←KPLiteralExceptionalResidue.rationalLift_unipotent,hf.2.1]
  rfl

def slotObservation : complexCore →ₗ[ℂ] C(KPAdditiveQuotient F,ℂ) where
  toFun v := ⟨fun q=>LiteralSource.coreResidue R P C (slot v)
    (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*g),
    slot_orbit_continuous R P C s x w hw g v⟩
  map_add' u v := by ext q;simp only [map_add,Pi.add_apply,ContinuousMap.add_apply];rfl
  map_smul' c v := by ext q;simp only [map_smul,Pi.smul_apply,ContinuousMap.smul_apply];rfl

include N  in
theorem slotObservation_continuous : Continuous (slotObservation R P C s x w hw g) := by
  obtain ⟨orders,B,hB,h⟩ := restrictedSlot_actual_orbit_bound R N P C  s x w hw g
  apply core_withSeminorms.continuous_normedSpace_rng C(KPAdditiveQuotient F,ℂ)
  refine ⟨orders,⟨B,hB.le⟩,fun v=>?_⟩
  apply (ContinuousMap.norm_le _ (mul_nonneg hB.le (apply_nonneg _ _))).mpr
  exact h v

def completedObservation : PrincipalSeries negativeParameter →L[ℂ] C(KPAdditiveQuotient F,ℂ) :=
  (⟨slotObservation R P C s x w hw g,slotObservation_continuous R N P C  s x w hw g⟩ :
    complexCore →L[ℂ] C(KPAdditiveQuotient F,ℂ)).extend smoothInclusion

theorem completedObservation_core (v : complexCore) :
    completedObservation R N P C  s x w hw g (smoothInclusion v)=
      slotObservation R P C s x w hw g v :=
  ContinuousLinearMap.extend_eq _ smoothInclusion_denseRange smoothInclusion_isUniformInducing v

theorem completedObservation_eq_output (v : PrincipalSeries negativeParameter)
    (q : KPAdditiveQuotient F) :
    completedObservation R N P C  s x w hw g v q=
      canonicalOutput R N P C  s x w hw
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*g) v := by
  refine smoothInclusion_denseRange.induction_on v ?_ ?_
  · exact isClosed_eq ((ContinuousMap.evalCLM ℂ q).continuous.comp
      (completedObservation R N P C  s x w hw g).continuous)
      (canonicalOutput R N P C  s x w hw _).continuous
  · intro u
    rw [completedObservation_core,canonicalOutput_core]
    rfl
end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
