module

public import DedekindZetaZeroFree.Theta.Periods.ProjectiveAction
public import DedekindZetaZeroFree.Theta.Whittaker.CompletedPeriodVectors

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
local instance backgroundRatioCoreAdd : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance backgroundRatioCoreModule : Module ℂ complexCore := Submodule.module complexCore
local instance backgroundRatioCoreTopology : TopologicalSpace complexCore := instTopologicalSpaceSubtype
local instance backgroundRatioPrincipalUniform : IsUniformAddGroup (PrincipalSeries negativeParameter) :=
  isUniformAddGroup_of_addCommGroup
local instance backgroundRatioCoreUniform : IsUniformAddGroup complexCore :=
  complexCore.toAddSubgroup.isUniformAddGroup

variable (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
variable (x : ∀j : s.val,LiteralSource.Plus R.A P C j.val)
variable (w : InfinitePlace F) (hw : Sum.inl w∈s.val)
variable (g : MomentSources.Group R)
local notation "slot" => restrictedSlotTensor R.A P C s x w hw

open KPCplxCharacterHaar KPCplxActualImage KPCplxWhittakerUnique
local notation "dq" => KPWildKernelUpperBound.quotientHaar F

open _root_.DedekindZetaZeroFree.KPWildComplexWhittakerDictionary renaming continuousWhittaker_comparison → KPWildComplexWhittakerDictionary.continuousWhittaker_comparison

include N  in
theorem restrictedSlotPeriod_background_ratio
    (hg : ∀z:ℂ,g*actualMatrixSlot R w (upperUnipotent z)=
      actualMatrixSlot R w (upperUnipotent z)*g)
    (M : Theta traceFrequency →L[ℂ] ℂ)
    (hM : M ∈ whittakerSpace traceFrequency traceCharacter)
    (v0 : complexCore) (hv0 : M (harmonicInclusion v0) ≠ 0)
    (a : ComplexPGL2) :
    restrictedSlotPeriod R P C s x w hw (g*projectiveSlot R w a) v0=
      (M (imageAction traceFrequency a (harmonicInclusion v0))/M (harmonicInclusion v0))*
        restrictedSlotPeriod R P C s x w hw g v0 := by
  let L := actualWhittakerAt R N P C  s x w hw g
  have hL : L∈whittakerSpace traceFrequency traceCharacter :=
    actualWhittakerAt_mem R N P C  s x w hw g hg
  have he := KPWildComplexWhittakerDictionary.continuousWhittaker_comparison
    traceFrequency traceCharacter traceCharacter_continuous traceCharacter_ne_one
    L M hL hM v0 hv0
  rw [restrictedSlotPeriod_projective R N P C ]
  rw [←actualWhittakerAt_core R N P C  s x w hw g v0]
  change L (imageAction traceFrequency a (harmonicInclusion v0))=
    (M (imageAction traceFrequency a (harmonicInclusion v0))/M (harmonicInclusion v0))*
      L (harmonicInclusion v0)
  rw [he]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
  field_simp [hv0]
  <;> ring

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
