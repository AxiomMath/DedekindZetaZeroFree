module

public import DedekindZetaZeroFree.Theta.Periods.FourierCompletion
public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.UpperUnipotentAction

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
local instance periodWhittakerCoreAdd : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance periodWhittakerCoreModule : Module ℂ complexCore := Submodule.module complexCore
local instance periodWhittakerCoreTopology : TopologicalSpace complexCore := instTopologicalSpaceSubtype
local instance periodWhittakerPrincipalUniform : IsUniformAddGroup (PrincipalSeries negativeParameter) :=
  isUniformAddGroup_of_addCommGroup
local instance periodWhittakerCoreUniform : IsUniformAddGroup complexCore :=
  complexCore.toAddSubgroup.isUniformAddGroup

variable (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
variable (x : ∀j : s.val,LiteralSource.Plus R.A P C j.val)
variable (w : InfinitePlace F) (hw : Sum.inl w∈s.val)
variable (g : MomentSources.Group R)
local notation "slot" => restrictedSlotTensor R.A P C s x w hw

open KPCplxCharacterHaar KPCplxActualImage KPCplxWhittakerUnique
local notation "dq" => KPWildKernelUpperBound.quotientHaar F

theorem completedPeriod_upper_action (z : ℂ) (v : PrincipalSeries negativeParameter) :
    completedPeriod R N P C  s x w hw
      (g*actualMatrixSlot R w (upperUnipotent z)) v=
    completedPeriod R N P C  s x w hw g
      (KPCplxPrincipalSeriesCharts.rightTranslate negativeParameter (upperUnipotent z) v) := by
  rw [completedPeriod_integral,completedPeriod_integral]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [←mul_assoc,canonicalOutput_upper_action]

theorem completedPeriod_whittaker (z : ℂ) (v : PrincipalSeries negativeParameter) :
    completedPeriod R N P C  s x w hw 1
      (KPCplxPrincipalSeriesCharts.rightTranslate negativeParameter (upperUnipotent z) v)=
      (traceCharacter z:ℂ)*completedPeriod R N P C  s x w hw 1 v := by
  rw [←completedPeriod_upper_action,one_mul,actualMatrixSlot_root]
  simpa only [mul_one,actualRootAdele_character] using
    completedPeriod_left_root R N P C  s x w hw 1 (actualRootAdele R w z) v

def actualWhittakerExtension : Theta traceFrequency →L[ℂ] ℂ :=
  (completedPeriod R N P C  s x w hw 1).comp
    ⟨(imageSubmodule traceFrequency).subtype,continuous_subtype_val⟩

theorem actualWhittakerExtension_mem :
    actualWhittakerExtension R N P C  s x w hw ∈
      whittakerSpace traceFrequency traceCharacter := by
  intro z v
  change completedPeriod R N P C  s x w hw 1
    (KPCplxPrincipalSeriesCharts.pi negativeParameter (Matrix.ProjGenLinGroup.mk (upperUnipotent z)) v.val)=_
  change completedPeriod R N P C  s x w hw 1
    (KPCplxPrincipalSeriesCharts.rightTranslate negativeParameter (upperUnipotent z) v.val)=_
  exact completedPeriod_whittaker R N P C  s x w hw z v.val

theorem actualWhittakerExtension_core (v : complexCore) :
    actualWhittakerExtension R N P C  s x w hw (harmonicInclusion v)=
      restrictedSlotPeriod R P C s x w hw 1 v := by
  exact completedPeriod_core R N P C  s x w hw 1 v

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
