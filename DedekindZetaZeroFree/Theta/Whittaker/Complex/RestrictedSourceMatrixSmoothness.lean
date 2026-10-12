module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.SmoothEvaluationExtension

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal Matrix.Norms.Elementwise ContDiff
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts LiteralSource
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
attribute [local irreducible] CanonicalStageSlot.negative
local instance : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance : Module ℂ complexCore := Submodule.module complexCore
local instance : TopologicalSpace complexCore := instTopologicalSpaceSubtype
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)
variable (s : RestrictedTensorSimple.Level (LiteralSource.bad A P C))
variable (x : ∀ j : s.val, LiteralSource.Plus A P C j.val) (w : InfinitePlace F)
variable (hw : Sum.inl w ∈ s.val)

def wholeRawSlot (g : LiteralSource.Raw A) : PrincipalSeries negativeParameter →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ (⟨g, Set.mem_singleton g⟩ : ({g} : Set (LiteralSource.Raw A)))).comp
    (rawSmoothObservation A P C s x w {g} isCompact_singleton)

theorem wholeRawSlot_core (g : LiteralSource.Raw A) (v : complexCore) :
    wholeRawSlot A P C s x w g v.val =
      rawCoreInsertion A P C (restrictedSlotTensor A P C s x w hw v) g :=
  rawSmoothObservation_core A P C s x w hw {g} isCompact_singleton v ⟨g, rfl⟩

include hw in

theorem wholeRawSlot_compact (K : Set (LiteralSource.Raw A)) (hK : IsCompact K)
    (g : K) (f : PrincipalSeries negativeParameter) :
    wholeRawSlot A P C s x w g.val f = rawSmoothObservation A P C s x w K hK f g := by
  let L := (ContinuousMap.evalCLM ℂ g).comp (rawSmoothObservation A P C s x w K hK)
  have he : (wholeRawSlot A P C s x w g.val : PrincipalSeries negativeParameter → ℂ) = L := by
    apply smoothInclusion_denseRange.equalizer (wholeRawSlot A P C s x w g.val).continuous L.continuous
    funext v
    exact (wholeRawSlot_core A P C s x w hw g.val v).trans
      (rawSmoothObservation_core A P C s x w hw K hK v g).symm
  exact congrFun he f

include hw in

theorem wholeRawSlot_compact_bound (K : Set (LiteralSource.Raw A)) (hK : IsCompact K) :
    ∃ orders : Finset ℕ, ∃ B : ℝ≥0, B ≠ 0 ∧
      ∀ (f : PrincipalSeries negativeParameter) (g : LiteralSource.Raw A), g ∈ K →
        ‖wholeRawSlot A P C s x w g f‖ ≤
          B * (orders.sup (chartSeminorm negativeParameter)) f := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨orders, B, hB, hb⟩ := rawSmoothObservation_bound A P C s x w K hK
  refine ⟨orders, B, hB, fun f g hg => ?_⟩
  rw [wholeRawSlot_compact A P C s x w hw K hK ⟨g,hg⟩ f]
  exact ((rawSmoothObservation A P C s x w K hK f).norm_coe_le_norm ⟨g,hg⟩).trans (hb f)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
