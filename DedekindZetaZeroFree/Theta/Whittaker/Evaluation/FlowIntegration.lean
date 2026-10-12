module

public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.DiagonalDerivative
public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.TranslationFlow

@[expose] public section

noncomputable section
open scoped Classical Topology
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts ComplexLines
open Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {α : Type*} [TopologicalSpace α]
variable (E : complexCore →ₗ[ℂ] (α → ℂ)) (he : ∀v,Continuous (E v)) (hb : CompactBound E)

include he in
theorem completed_flow_constant
    (X : Matrix (Fin 2) (Fin 2) ℂ) (q : ℝ → α) (hq : Continuous q)
    (hd : ∀v : PrincipalSeries negativeParameter, ∀t : ℝ,
      HasDerivAt (fun r=>extendedEvaluation E hb (q r) v)
        (extendedEvaluation E hb (q t) (NativeComplexHCOperators.derivative negativeParameter X v)) t)
    (v : PrincipalSeries negativeParameter) (t : ℝ) :
    extendedEvaluation E hb (q t)
      (KPCplxPrincipalSeriesCharts.rightTranslate negativeParameter (sourceFlow (-X) t) v)=
    extendedEvaluation E hb (q 0) v := by
  let vt := fun r=>KPCplxPrincipalSeriesCharts.rightTranslate negativeParameter (sourceFlow (-X) r) v
  let f := fun r=>extendedEvaluation E hb (q r) (vt r)
  have hv0 : vt 0=v := by
    apply Subtype.ext
    funext g
    simp [vt,sourceFlow_zero,KPCplxPrincipalSeriesCharts.rightTranslate]
  have hder (a : ℝ) : HasDerivAt f 0 a := by
    let vr := fun r=>KPCplxPrincipalSeriesCharts.rightTranslate negativeParameter (sourceFlow (-X) r) (vt a)
    have hvr (r : ℝ) : vr r=vt (r+a) := sourceTranslate_add negativeParameter (-X) r a v
    have hz : vr 0=vt a := by simpa only [zero_add] using hvr 0
    have hs : Tendsto (fun r : ℝ=>(r:ℂ)⁻¹ • (vr r-vr 0)) (𝓝[≠] 0)
        (𝓝 (NativeComplexHCOperators.derivative negativeParameter (-X) (vt a))) := by
      rw [hz]
      exact source_flow_difference negativeParameter (-X) (vt a)
    have hh := hd (vt a) a
    have hh0 := (show HasDerivAt (fun r=>extendedEvaluation E hb (q r) (vt a))
        (extendedEvaluation E hb (q a) (NativeComplexHCOperators.derivative negativeParameter X (vt a))) (0+a) from by simpa using hh).comp_add_const 0 a
    have H := diagonal_derivative E he hb (fun r=>q (r+a)) (hq.comp (continuous_id.add_const a)) vr
      (NativeComplexHCOperators.derivative negativeParameter (-X) (vt a)) hs
      (extendedEvaluation E hb (q a) (NativeComplexHCOperators.derivative negativeParameter X (vt a)))
      (by simpa only [hz] using hh0)
    simp only [zero_add,sourceDerivative_neg,map_neg,neg_add_cancel] at H
    have He : (fun r=>extendedEvaluation E hb (q (r+a)) (vr r))=fun r=>f (r+a) := by
      funext r
      rw [hvr]
    rw [He] at H
    have H0 : HasDerivAt (fun r=>f (r+a)) 0 (a-a) := by simpa using H
    have H1 := H0.comp_sub_const a a
    simpa only [sub_add_cancel] using H1
  have hc := is_const_of_deriv_eq_zero (fun a=>(hder a).differentiableAt) (fun a=>(hder a).deriv) t 0
  simpa only [f,hv0] using hc

include he in
theorem completed_flow_action
    (X : Matrix (Fin 2) (Fin 2) ℂ) (q : ℝ → α) (hq : Continuous q)
    (hd : ∀v : PrincipalSeries negativeParameter, ∀t : ℝ,
      HasDerivAt (fun r=>extendedEvaluation E hb (q r) v)
        (extendedEvaluation E hb (q t) (NativeComplexHCOperators.derivative negativeParameter X v)) t)
    (v : PrincipalSeries negativeParameter) (t : ℝ) :
    extendedEvaluation E hb (q t) v=extendedEvaluation E hb (q 0)
      (KPCplxPrincipalSeriesCharts.rightTranslate negativeParameter (sourceFlow X t) v) := by
  have h := completed_flow_constant E he hb X q hq hd
    (KPCplxPrincipalSeriesCharts.rightTranslate negativeParameter (sourceFlow X t) v) t
  rw [sourceTranslate_inverse] at h
  exact h
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
