module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Flows.LowerUnipotent
public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.UpperUnipotentAction
public import DedekindZetaZeroFree.Algebra.Groups.PGLTransvectionGeneration

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

theorem canonicalOutput_lower_action (g : MomentSources.Group R) (z : ℂ) (v : PrincipalSeries negativeParameter) :
    canonicalOutput R N P C  s x w hw (g*actualMatrixSlot R w (lowerGL z)) v=
      canonicalOutput R N P C  s x w hw g
        (KPCplxPrincipalSeriesCharts.rightTranslate negativeParameter (lowerGL z) v) := by
  rw [lowerGL_flow_factor,actualMatrixSlot_mul,←mul_assoc,canonicalOutput_slot_flow,canonicalOutput_slot_flow]
  congr 1
  apply Subtype.ext
  funext a
  change v (a * _ * _)=v (a * (_ * _))
  rw [mul_assoc]

def projectiveSlot (p : KPCplxCharacterHaar.ComplexPGL2) : MomentSources.Group R :=
  archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12 (Function.update 1 w p)

theorem projectiveSlot_mk (a : KPCplxCharacterHaar.ComplexGL2) :
    projectiveSlot R w (Matrix.ProjGenLinGroup.mk a)=actualMatrixSlot R w a := by
  unfold projectiveSlot actualMatrixSlot
  congr 1
  funext u
  by_cases h:u=w
  · subst u;simp
  · simp [h]

theorem projectiveSlot_mul (a b : KPCplxCharacterHaar.ComplexPGL2) :
    projectiveSlot R w (a*b)=projectiveSlot R w a*projectiveSlot R w b := by
  unfold projectiveSlot
  rw [←(archimedean_insertion_properties F R.A.zeta12 R.A.primitive_zeta12).2.1]
  congr 1
  funext u
  by_cases h:u=w
  · subst u;simp
  · simp [h]

theorem canonicalOutput_projective_action (a : KPCplxCharacterHaar.ComplexPGL2)
    (g : MomentSources.Group R) (v : PrincipalSeries negativeParameter) :
    canonicalOutput R N P C  s x w hw (g*projectiveSlot R w a) v=
      canonicalOutput R N P C  s x w hw g (KPCplxPrincipalSeriesCharts.pi negativeParameter a v) := by
  have H : ∀a : KPCplxCharacterHaar.ComplexPGL2, ∀g v,
      canonicalOutput R N P C  s x w hw (g*projectiveSlot R w a) v=
        canonicalOutput R N P C  s x w hw g (KPCplxPrincipalSeriesCharts.pi negativeParameter a v) := by
    intro a
    apply projective_transvection_induction (fun a=>∀g v,
      canonicalOutput R N P C  s x w hw (g*projectiveSlot R w a) v=
        canonicalOutput R N P C  s x w hw g (KPCplxPrincipalSeriesCharts.pi negativeParameter a v))
    · intro i j hij z g v
      change canonicalOutput R N P C  s x w hw
        (g*projectiveSlot R w (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij z)))) v=_
      rw [projectiveSlot_mk]
      change _ = canonicalOutput R N P C  s x w hw g
        (KPCplxPrincipalSeriesCharts.rightTranslate negativeParameter
          (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij z)) v)
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · have he : Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection (i:=0) (j:=1) hij z)=KPCplxCharacterHaar.upperUnipotent z := by
          apply Units.ext
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.toGL,Matrix.SpecialLinearGroup.transvection_coe,KPCplxCharacterHaar.upperUnipotent]
        rw [he]
        exact canonicalOutput_upper_action R N P C  s x w hw g z v
      · exact canonicalOutput_lower_action R N P C  s x w hw g z v
      · exact (hij rfl).elim
    · intro a b ha hb g v
      rw [projectiveSlot_mul,←mul_assoc,hb,ha,pi_mul]
  exact H a g v
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
