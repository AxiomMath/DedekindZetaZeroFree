module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.ProjectiveGroupAction
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
local instance periodProjectiveCoreAdd : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance periodProjectiveCoreModule : Module ℂ complexCore := Submodule.module complexCore
local instance periodProjectiveCoreTopology : TopologicalSpace complexCore := instTopologicalSpaceSubtype
local instance periodProjectivePrincipalUniform : IsUniformAddGroup (PrincipalSeries negativeParameter) :=
  isUniformAddGroup_of_addCommGroup
local instance periodProjectiveCoreUniform : IsUniformAddGroup complexCore :=
  complexCore.toAddSubgroup.isUniformAddGroup

variable (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
variable (x : ∀j : s.val,LiteralSource.Plus R.A P C j.val)
variable (w : InfinitePlace F) (hw : Sum.inl w∈s.val)
variable (g : MomentSources.Group R)
local notation "slot" => restrictedSlotTensor R.A P C s x w hw

open KPCplxCharacterHaar KPCplxActualImage KPCplxWhittakerUnique
local notation "dq" => KPWildKernelUpperBound.quotientHaar F

theorem completedPeriod_projective_action (a : ComplexPGL2) (v : PrincipalSeries negativeParameter) :
    completedPeriod R N P C  s x w hw (g*projectiveSlot R w a) v=
    completedPeriod R N P C  s x w hw g (KPCplxPrincipalSeriesCharts.pi negativeParameter a v) := by
  rw [completedPeriod_integral,completedPeriod_integral]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [←mul_assoc,canonicalOutput_projective_action]

theorem restrictedSlotPeriod_projective (a : ComplexPGL2) (v : complexCore) :
    restrictedSlotPeriod R P C s x w hw (g*projectiveSlot R w a) v=
    completedPeriod R N P C  s x w hw g
      (KPCplxPrincipalSeriesCharts.pi negativeParameter a (smoothInclusion v)) := by
  rw [←completedPeriod_core R N P C  s x w hw]
  exact completedPeriod_projective_action R N P C  s x w hw g a (smoothInclusion v)

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
