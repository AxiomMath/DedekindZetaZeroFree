module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.FlowAction
public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.OrbitContinuity
public import DedekindZetaZeroFree.Theta.Periods.RestrictedTensorIntegration
public import DedekindZetaZeroFree.Adeles.Characters.RootSubgroupEmbedding

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
local instance rootActionCoreAdd : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance rootActionCoreModule : Module ℂ complexCore := Submodule.module complexCore
local instance rootActionCoreTopology : TopologicalSpace complexCore := instTopologicalSpaceSubtype
local instance rootActionPrincipalUniform : IsUniformAddGroup (PrincipalSeries negativeParameter) :=
  isUniformAddGroup_of_addCommGroup
local instance rootActionCoreUniform : IsUniformAddGroup complexCore :=
  complexCore.toAddSubgroup.isUniformAddGroup

variable (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
variable (x : ∀j : s.val,LiteralSource.Plus R.A P C j.val)
variable (w : InfinitePlace F) (hw : Sum.inl w∈s.val)
variable (g : MomentSources.Group R)
local notation "slot" => restrictedSlotTensor R.A P C s x w hw

open KPSmoothActualFlowData KPCplxCharacterHaar
open KPContActualSphericalRightFieldIdentification KPMsClearedTruncationL2.NativeWordBridge
open HCGeneration
open scoped Matrix.Norms.Operator
open _root_.DedekindZetaZeroFree.RootDerivatives renaming exp_upper → RootDerivatives.exp_upper

theorem sourceFlow_upper_real (t : ℝ) : sourceFlow (KPSmoothActualFlowData.basisMatrix 2) t=upperUnipotent (t:ℂ) := by
  apply Units.ext
  change NormedSpace.exp ((t:ℂ) • KPSmoothActualFlowData.basisMatrix 2)=_
  have hm : (t:ℂ) • KPSmoothActualFlowData.basisMatrix 2=(!![0,(t:ℂ);0,0] : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [KPSmoothActualFlowData.basisMatrix,sl2Matrix,Matrix.smul_apply,smul_eq_mul]
  rw [hm,RootDerivatives.exp_upper]
  rfl

theorem sourceFlow_upper_imag (t : ℝ) : sourceFlow (KPSmoothActualFlowData.basisMatrix 3) t=upperUnipotent (Complex.I*(t:ℂ)) := by
  apply Units.ext
  change NormedSpace.exp ((t:ℂ) • KPSmoothActualFlowData.basisMatrix 3)=_
  have hm : (t:ℂ) • KPSmoothActualFlowData.basisMatrix 3=(!![0,Complex.I*(t:ℂ);0,0] : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [KPSmoothActualFlowData.basisMatrix,sl2Matrix,Matrix.smul_apply,smul_eq_mul,mul_comm]
  rw [hm,RootDerivatives.exp_upper]
  rfl

theorem actualMatrixSlot_mul (a b : ComplexGL2) :
    actualMatrixSlot R w (a*b)=actualMatrixSlot R w a*actualMatrixSlot R w b := by
  unfold actualMatrixSlot
  rw [←(archimedean_insertion_properties F ζ hζ).2.1]
  congr 1
  funext u
  by_cases hu:u=w
  · subst u;simp
  · simp [hu]

theorem actualFlow_slot (i : Fin 6) (t : ℝ) :
    archimedeanInsertion F ζ hζ
      (flow F (wordIndexEquiv F ((actualLieIndexEquiv (F:=F)).symm (w,i))) t)=
      actualMatrixSlot R w (sourceFlow (KPSmoothActualFlowData.basisMatrix i) t) := by
  have he : wordIndexEquiv F ((actualLieIndexEquiv (F:=F)).symm (w,i))=(w,i) := by
    change actualLieIndexEquiv ((actualLieIndexEquiv (F:=F)).symm (w,i))=(w,i)
    exact Equiv.apply_symm_apply _ _
  rw [he,ResidualPrincipalSlices.flow_matrix_update]
  rfl

theorem canonicalOutput_slot_flow (i : Fin 6)
    (v : PrincipalSeries negativeParameter) (t : ℝ) :
    canonicalOutput R N P C  s x w hw (g*actualMatrixSlot R w (sourceFlow (KPSmoothActualFlowData.basisMatrix i) t)) v=
      canonicalOutput R N P C  s x w hw g
        (KPCplxPrincipalSeriesCharts.rightTranslate negativeParameter (sourceFlow (KPSmoothActualFlowData.basisMatrix i) t) v) := by
  rw [←actualFlow_slot]
  exact canonicalOutput_flow_action R N P C  s x w hw i v g t

theorem canonicalOutput_upper_action (z : ℂ) (v : PrincipalSeries negativeParameter) :
    canonicalOutput R N P C  s x w hw (g*actualMatrixSlot R w (upperUnipotent z)) v=
      canonicalOutput R N P C  s x w hw g
        (KPCplxPrincipalSeriesCharts.rightTranslate negativeParameter (upperUnipotent z) v) := by
  have he : upperUnipotent z=sourceFlow (KPSmoothActualFlowData.basisMatrix 2) z.re*sourceFlow (KPSmoothActualFlowData.basisMatrix 3) z.im := by
    rw [sourceFlow_upper_real,sourceFlow_upper_imag]
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent,Matrix.mul_apply,Fin.sum_univ_two]
    exact (Complex.re_add_im z).symm.trans (by ring)
  rw [he,actualMatrixSlot_mul,←mul_assoc,canonicalOutput_slot_flow,canonicalOutput_slot_flow]
  congr 1
  apply Subtype.ext
  funext a
  change v (a * _ * _)=v (a * (_ * _))
  rw [mul_assoc]
end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
