module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Complex.OperatorWordBounds
public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.CompactUniformLimits

@[expose] public section

noncomputable section
open scoped Classical Topology NNReal
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts ComplexLines
local instance : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance : Module ℂ complexCore := Submodule.module complexCore
local instance : TopologicalSpace complexCore := instTopologicalSpaceSubtype
variable {α : Type*} [TopologicalSpace α]
variable (E : complexCore →ₗ[ℂ] (α → ℂ)) (hb : CompactBound E)

theorem extendedEvaluation_operator
    (A : complexCore →ₗ[ℂ] complexCore)
    (T : PrincipalSeries negativeParameter →L[ℂ] PrincipalSeries negativeParameter)
    (hT : ∀v,smoothInclusion (A v)=T (smoothInclusion v))
    (hA : CompactBound (E.comp A)) (g : α) (v : PrincipalSeries negativeParameter) :
    extendedEvaluation (E.comp A) hA g v = extendedEvaluation E hb g (T v) := by
  refine smoothInclusion_denseRange.induction_on v ?_ ?_
  · exact isClosed_eq (extendedEvaluation (E.comp A) hA g).continuous
      ((extendedEvaluation E hb g).continuous.comp T.continuous)
  · intro u
    rw [extendedEvaluation_core,← hT,extendedEvaluation_core]
    rfl

include hb in
theorem compactBound_operator (A : complexCore →ₗ[ℂ] complexCore) (hA : Continuous A) :
    CompactBound (E.comp A) := by
  intro K hK
  obtain ⟨orders,B,h⟩ := hb K hK
  let Q : Seminorm ℂ complexCore := (orders.sup coreSeminorm).comp A
  have hQ : Continuous Q :=
    (Seminorm.continuous_finsetSup (fun i _=>core_withSeminorms.continuous_seminorm i)).comp hA
  obtain ⟨orders₁,B₁,_,hb₁⟩ := Seminorm.bound_of_continuous core_withSeminorms Q hQ
  refine ⟨orders₁,B*B₁,?_⟩
  intro v g hg
  calc
    ‖(E.comp A) v g‖ ≤ B*(orders.sup coreSeminorm) (A v) := h (A v) g hg
    _ ≤ B*(B₁*(orders₁.sup coreSeminorm) v) := mul_le_mul_of_nonneg_left (hb₁ v) B.coe_nonneg
    _ = (B*B₁ : ℝ≥0)*(orders₁.sup coreSeminorm) v := by simp only [NNReal.coe_mul];ring
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
