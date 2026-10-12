module

public import DedekindZetaZeroFree.Theta.Whittaker.CompletedPeriodCovariance

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
local instance backgroundWhittakerCoreAdd : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance backgroundWhittakerCoreModule : Module ℂ complexCore := Submodule.module complexCore
local instance backgroundWhittakerCoreTopology : TopologicalSpace complexCore := instTopologicalSpaceSubtype
local instance backgroundWhittakerPrincipalUniform : IsUniformAddGroup (PrincipalSeries negativeParameter) :=
  isUniformAddGroup_of_addCommGroup
local instance backgroundWhittakerCoreUniform : IsUniformAddGroup complexCore :=
  complexCore.toAddSubgroup.isUniformAddGroup

variable (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
variable (x : ∀j : s.val,LiteralSource.Plus R.A P C j.val)
variable (w : InfinitePlace F) (hw : Sum.inl w∈s.val)
variable (g : MomentSources.Group R)
local notation "slot" => restrictedSlotTensor R.A P C s x w hw

open KPCplxCharacterHaar KPCplxActualImage KPCplxWhittakerUnique
local notation "dq" => KPWildKernelUpperBound.quotientHaar F

theorem completedPeriod_whittaker_at
    (hg : ∀z:ℂ,g*actualMatrixSlot R w (upperUnipotent z)=
      actualMatrixSlot R w (upperUnipotent z)*g)
    (z : ℂ) (v : PrincipalSeries negativeParameter) :
    completedPeriod R N P C  s x w hw g
      (KPCplxPrincipalSeriesCharts.rightTranslate negativeParameter (upperUnipotent z) v)=
      (traceCharacter z:ℂ)*completedPeriod R N P C  s x w hw g v := by
  rw [←completedPeriod_upper_action,hg,actualMatrixSlot_root]
  simpa only [actualRootAdele_character] using
    completedPeriod_left_root R N P C  s x w hw g (actualRootAdele R w z) v

def actualWhittakerAt : Theta traceFrequency →L[ℂ] ℂ :=
  (completedPeriod R N P C  s x w hw g).comp
    ⟨(imageSubmodule traceFrequency).subtype,continuous_subtype_val⟩

theorem actualWhittakerAt_mem
    (hg : ∀z:ℂ,g*actualMatrixSlot R w (upperUnipotent z)=
      actualMatrixSlot R w (upperUnipotent z)*g) :
    actualWhittakerAt R N P C  s x w hw g ∈
      whittakerSpace traceFrequency traceCharacter := by
  intro z v
  change completedPeriod R N P C  s x w hw g
    (KPCplxPrincipalSeriesCharts.rightTranslate negativeParameter (upperUnipotent z) v.val)=_
  exact completedPeriod_whittaker_at R N P C  s x w hw g hg z v.val

theorem actualWhittakerAt_core (v : complexCore) :
    actualWhittakerAt R N P C  s x w hw g (harmonicInclusion v)=
      restrictedSlotPeriod R P C s x w hw g v := by
  exact completedPeriod_core R N P C  s x w hw g v

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
