module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.SmoothExtensionByHarmonicDensity

@[expose] public section

noncomputable section
open scoped Classical Topology NNReal
open Filter
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts ComplexLines
local instance : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance : Module ℂ complexCore := Submodule.module complexCore
local instance : TopologicalSpace complexCore := instTopologicalSpaceSubtype
local instance : IsUniformAddGroup (PrincipalSeries negativeParameter) := isUniformAddGroup_of_addCommGroup
local instance : IsUniformAddGroup complexCore := complexCore.toAddSubgroup.isUniformAddGroup
variable {α : Type*} [TopologicalSpace α]
variable (E : complexCore →ₗ[ℂ] (α → ℂ))

def CompactBound : Prop := ∀K : Set α, IsCompact K →
  ∃ orders : Finset ℕ, ∃ B : ℝ≥0, ∀v a, a∈K → ‖E v a‖ ≤ B*(orders.sup coreSeminorm) v

def evaluation (a : α) : complexCore →ₗ[ℂ] ℂ := (LinearMap.proj a).comp E

theorem evaluation_continuous (hb : CompactBound E) (a : α) : Continuous (evaluation E a) := by
  obtain ⟨orders,B,h⟩ := hb {a} isCompact_singleton
  exact continuous_of_native_bound (evaluation E a) orders B (fun v=>h v a (Set.mem_singleton a))

def extendedEvaluation (hb : CompactBound E) (a : α) : PrincipalSeries negativeParameter →L[ℂ] ℂ :=
  (⟨evaluation E a,evaluation_continuous E hb a⟩ : complexCore →L[ℂ] ℂ).extend smoothInclusion

theorem extendedEvaluation_core (hb : CompactBound E) (a : α) (v : complexCore) :
    extendedEvaluation E hb a (smoothInclusion v)=E v a := by
  exact ContinuousLinearMap.extend_eq _ smoothInclusion_denseRange smoothInclusion_isUniformInducing v

def compactObservation (he : ∀v,Continuous (E v)) (K : Set α) : complexCore →ₗ[ℂ] C(K,ℂ) where
  toFun v := ⟨fun a=>E v a.val,(he v).comp continuous_subtype_val⟩
  map_add' u v := by ext a;exact congrFun (E.map_add u v) a.val
  map_smul' c v := by ext a;exact congrFun (E.map_smul c v) a.val

include E in
theorem compactObservation_continuous (he : ∀v,Continuous (E v)) (hb : CompactBound E)
    (K : Set α) (hK : IsCompact K) : Continuous (compactObservation E he K) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨orders,B,h⟩ := hb K hK
  apply core_withSeminorms.continuous_normedSpace_rng C(K,ℂ)
  refine ⟨orders,B,fun v=>?_⟩
  apply (ContinuousMap.norm_le _ (mul_nonneg B.coe_nonneg (apply_nonneg _ _))).mpr
  intro a
  exact h v a.val a.property

def extendedCompact (he : ∀v,Continuous (E v)) (hb : CompactBound E)
    (K : Set α) (hK : IsCompact K) : PrincipalSeries negativeParameter →L[ℂ] C(K,ℂ) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact (⟨compactObservation E he K,compactObservation_continuous E he hb K hK⟩ :
    complexCore →L[ℂ] C(K,ℂ)).extend smoothInclusion

theorem extendedCompact_core (he : ∀v,Continuous (E v)) (hb : CompactBound E)
    (K : Set α) (hK : IsCompact K) (v : complexCore) :
    extendedCompact E he hb K hK (smoothInclusion v)=compactObservation E he K v := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact ContinuousLinearMap.extend_eq _ smoothInclusion_denseRange smoothInclusion_isUniformInducing v

theorem extendedCompact_eval (he : ∀v,Continuous (E v)) (hb : CompactBound E)
    (K : Set α) (hK : IsCompact K) (v : PrincipalSeries negativeParameter) (a : K) :
    extendedCompact E he hb K hK v a = extendedEvaluation E hb a.val v := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  refine smoothInclusion_denseRange.induction_on v ?_ ?_
  · exact isClosed_eq ((ContinuousMap.evalCLM ℂ a).continuous.comp (extendedCompact E he hb K hK).continuous)
      (extendedEvaluation E hb a.val).continuous
  · intro u
    rw [extendedCompact_core,extendedEvaluation_core]
    rfl
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
