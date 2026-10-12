module

public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.ContinuousExtension

@[expose] public section

noncomputable section
open scoped Classical Topology
open Filter
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts ComplexLines
local instance : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance : Module ℂ complexCore := Submodule.module complexCore
local instance : TopologicalSpace complexCore := instTopologicalSpaceSubtype
variable {α : Type*} [TopologicalSpace α]
variable (E : complexCore →ₗ[ℂ] (α → ℂ)) (he : ∀v,Continuous (E v)) (hb : CompactBound E)

theorem harmonic_compact_limit (K : Set α) (hK : IsCompact K)
    (v : PrincipalSeries negativeParameter) (a : ℕ → complexCore)
    (ha : Tendsto (fun n=>smoothInclusion (a n)) atTop (𝓝 v)) :
    Tendsto (fun n=>compactObservation E he K (a n)) atTop (𝓝 (extendedCompact E he hb K hK v)) := by
  have ht := ((extendedCompact E he hb K hK).continuous.tendsto v).comp ha
  simpa only [Function.comp_def,extendedCompact_core] using ht

include he in
theorem extendedOutput_continuousOn (K : Set α) (hK : IsCompact K)
    (v : PrincipalSeries negativeParameter) :
    ContinuousOn (fun a=>extendedEvaluation E hb a v) K := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (fun a : K=>extendedEvaluation E hb a.val v)=extendedCompact E he hb K hK v := by
    funext a
    exact (extendedCompact_eval E he hb K hK v a).symm
  change Continuous (fun a : K=>extendedEvaluation E hb a.val v)
  rw [heq]
  exact (extendedCompact E he hb K hK v).continuous

include he in
theorem extendedOutput_continuous [LocallyCompactSpace α] (v : PrincipalSeries negativeParameter) :
    Continuous (fun a=>extendedEvaluation E hb a v) := by
  rw [continuous_iff_continuousAt]
  intro a
  obtain ⟨K,hK,hKa⟩ := exists_compact_mem_nhds a
  exact (extendedOutput_continuousOn E he hb K hK v).continuousAt hKa

def completedOutput [LocallyCompactSpace α] : PrincipalSeries negativeParameter →ₗ[ℂ] C(α,ℂ) where
  toFun v := ⟨fun a=>extendedEvaluation E hb a v,extendedOutput_continuous E he hb v⟩
  map_add' u v := by ext a;exact (extendedEvaluation E hb a).map_add u v
  map_smul' c v := by ext a;exact (extendedEvaluation E hb a).map_smul c v

theorem completedOutput_core [LocallyCompactSpace α] (v : complexCore) (a : α) :
    completedOutput E he hb (smoothInclusion v) a=E v a := extendedEvaluation_core E hb a v
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
