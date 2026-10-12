module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.FlowDerivative
public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.FlowIntegration

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open MomentSources KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts ComplexLines
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

variable (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
variable (x : ∀j : s.val,LiteralSource.Plus R.A P C j.val)
variable (w : InfinitePlace F) (hw : Sum.inl w∈s.val)

open KPContActualSphericalRightFieldIdentification KPMsClearedTruncationL2.NativeWordBridge
open KPSmoothActualFlowData
open LiteralSource HCGeneration TensorActionSource
set_option maxHeartbeats 1800000

theorem canonicalOutput_flow_action (i : Fin 6)
    (v : PrincipalSeries negativeParameter) (g : KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12)
    (t : ℝ) :
    canonicalOutput R N P C  s x w hw
      (g*archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12
        (flow F (wordIndexEquiv F ((actualLieIndexEquiv (F:=F)).symm (w,i))) t)) v =
    canonicalOutput R N P C  s x w hw g
      (KPCplxPrincipalSeriesCharts.rightTranslate negativeParameter (sourceFlow (basisMatrix i) t) v) := by
  let E := actualSlot R P C s x w hw
  have he := actualSlot_continuous R P C s x w hw
  have hb := actualSlot_bound R N P C  s x w hw
  let b := (actualLieIndexEquiv (F:=F)).symm (w,i)
  let q : ℝ → KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12 := fun r=>
    g*archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12 (flow F (wordIndexEquiv F b) r)
  have hq : Continuous q := continuous_const.mul
    ((archimedean_insertion_properties F R.A.zeta12 R.A.primitive_zeta12).2.2.1.comp
      (flow_properties F _).2.2)
  have hd := fun v r=>canonicalOutput_flow_derivative R N P C  s x w hw i v g r
  have H := completed_flow_action E he hb (basisMatrix i) q hq hd v t
  have hq0 : q 0=g := by
    dsimp [q]
    rw [(flow_properties F _).1,(archimedean_insertion_properties F R.A.zeta12 R.A.primitive_zeta12).1,mul_one]
  rw [hq0] at H
  exact H
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
