module

public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.OperatorExtension
public import DedekindZetaZeroFree.Eisenstein.Induction.FlowDerivative

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
include N  in
theorem canonicalOutput_flow_derivative (i : Fin 6)
    (v : PrincipalSeries negativeParameter) (g : KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12)
    (t : ℝ) :
    HasDerivAt (fun r=>canonicalOutput R N P C  s x w hw
      (g*archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12
        (flow F (wordIndexEquiv F ((actualLieIndexEquiv (F:=F)).symm (w,i))) r)) v)
      (canonicalOutput R N P C  s x w hw
        (g*archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12
          (flow F (wordIndexEquiv F ((actualLieIndexEquiv (F:=F)).symm (w,i))) t))
        (NativeComplexHCOperators.derivative negativeParameter (basisMatrix i) v)) t := by
  let E := actualSlot R P C s x w hw
  have he := actualSlot_continuous R P C s x w hw
  have hb := actualSlot_bound R N P C  s x w hw
  let A := NativeComplexHCOperators.operators i
  have hA := compactBound_operator E hb A (native_operators_continuous i)
  let T : PrincipalSeries negativeParameter →L[ℂ] PrincipalSeries negativeParameter :=
    ⟨NativeComplexHCOperators.derivative negativeParameter (basisMatrix i),
      actualDerivative_continuous negativeParameter (basisMatrix i)⟩
  let b := (actualLieIndexEquiv (F:=F)).symm (w,i)
  let γ : ℝ → KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12 := fun r=>
    g*archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12 (flow F (wordIndexEquiv F b) r)
  have hγ : Continuous γ := continuous_const.mul
    ((archimedean_insertion_properties F R.A.zeta12 R.A.primitive_zeta12).2.2.1.comp
      (flow_properties F _).2.2)
  have hd (u : complexCore) (r : ℝ) : HasDerivAt (fun z=>E u (γ z)) ((E.comp A) u (γ r)) r := by
    have hh := raw_flow_derivative (E u) (LiteralSource.coreResidue_raw_automorphic R P C _).1 b g r
    have heq : actualRight F R.A.zeta12 R.A.primitive_zeta12 b (E u)=E (A u) :=
      restrictedSlot_residue_lie R P C N s x w hw i u
    rw [heq] at hh
    exact hh
  have H := extended_derivative_curve E he hb (E.comp A) (fun u=>he (A u)) hA γ hγ hd v t
  rw [extendedEvaluation_operator E hb A T (fun _=>rfl) hA] at H
  exact H
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
