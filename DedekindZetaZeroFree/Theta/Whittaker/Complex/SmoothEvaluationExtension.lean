module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.RestrictedTensorInsertionBounds

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts LiteralSource
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 8000000
set_option diagnostics true
attribute [local irreducible] CanonicalStageSlot.negative
local instance : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance : Module ℂ complexCore := Submodule.module complexCore
local instance : TopologicalSpace complexCore := instTopologicalSpaceSubtype
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)

 def compactHead (s : RestrictedTensorSimple.Level (LiteralSource.bad A P C))
    (K : Set (LiteralSource.Raw A)) (hK : IsCompact K) :=
  (exists_compact_reference_stage A P C s K hK).choose

def stageSmoothObservationLinear
    (t : RestrictedTensorSimple.Level (LiteralSource.bad A P C))
    (y : ∀ j : t.val, LiteralSource.Plus A P C j.val) (w : InfinitePlace F)
    (K : Set (LiteralSource.Raw A)) :
    PrincipalSeries negativeParameter →ₗ[ℂ] C(K, ℂ) where
  toFun f := ⟨fun g => CanonicalStageSlot.negative A P C t y g.val w f,
    ((CanonicalStageSlot.negative_raw_joint A P C t y w).comp
      (continuous_const.prodMk continuous_subtype_val))⟩
  map_add' := by intro f h; ext g; exact (CanonicalStageSlot.negative A P C t y g.val w).map_add f h
  map_smul' := by intro c f; ext g; exact (CanonicalStageSlot.negative A P C t y g.val w).map_smul c f

theorem stageSmoothObservationLinear_continuous
    (t : RestrictedTensorSimple.Level (LiteralSource.bad A P C))
    (y : ∀ j : t.val, LiteralSource.Plus A P C j.val) (w : InfinitePlace F)
    (K : Set (LiteralSource.Raw A)) : Continuous (stageSmoothObservationLinear A P C t y w K) := by
  exact ContinuousMap.continuous_of_continuous_uncurry _
    ((CanonicalStageSlot.negative_raw_joint A P C t y w).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

def stageSmoothObservation
    (t : RestrictedTensorSimple.Level (LiteralSource.bad A P C))
    (y : ∀ j : t.val, LiteralSource.Plus A P C j.val) (w : InfinitePlace F)
    (K : Set (LiteralSource.Raw A)) : PrincipalSeries negativeParameter →L[ℂ] C(K, ℂ) :=
  ⟨stageSmoothObservationLinear A P C t y w K,
    stageSmoothObservationLinear_continuous A P C t y w K⟩

def rawSmoothObservation
    (s : RestrictedTensorSimple.Level (LiteralSource.bad A P C))
    (x : ∀ j : s.val, LiteralSource.Plus A P C j.val) (w : InfinitePlace F)
    (K : Set (LiteralSource.Raw A)) (hK : IsCompact K) :
    PrincipalSeries negativeParameter →L[ℂ] C(K, ℂ) :=
  let t := compactHead A P C s K hK
  stageSmoothObservation A P C t (enlargedTuple A P C s t x) w K

theorem rawSmoothObservation_core
    (s : RestrictedTensorSimple.Level (LiteralSource.bad A P C))
    (x : ∀ j : s.val, LiteralSource.Plus A P C j.val) (w : InfinitePlace F)
    (hw : Sum.inl w ∈ s.val) (K : Set (LiteralSource.Raw A)) (hK : IsCompact K)
    (v : complexCore) (g : K) :
    rawSmoothObservation A P C s x w K hK v.val g =
      rawCoreInsertion A P C (restrictedSlotTensor A P C s x w hw v) g.val := by
  let t := compactHead A P C s K hK
  have hst : s ≤ t := (exists_compact_reference_stage A P C s K hK).choose_spec.1
  have ht := (exists_compact_reference_stage A P C s K hK).choose_spec.2 g.val g.property
  change CanonicalStageSlot.negative A P C t (enlargedTuple A P C s t x) g.val w v.val = _
  rw [restrictedSlotTensor_enlarge A P C s t hst x w hw v,
    restrictedSlot_raw_pin A P C t _ w (hst hw) g.val ht v]

theorem rawSmoothObservation_bound
    (s : RestrictedTensorSimple.Level (LiteralSource.bad A P C))
    (x : ∀ j : s.val, LiteralSource.Plus A P C j.val) (w : InfinitePlace F)
    (K : Set (LiteralSource.Raw A)) (hK : IsCompact K) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ orders : Finset ℕ, ∃ B : ℝ≥0, B ≠ 0 ∧
      ∀ f : PrincipalSeries negativeParameter,
        ‖rawSmoothObservation A P C s x w K hK f‖ ≤
          B * (orders.sup (chartSeminorm negativeParameter)) f := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let t := compactHead A P C s K hK
  obtain ⟨orders, B, hB, hb⟩ := CanonicalStageSlot.negative_raw_compact_bound
    A P C t (enlargedTuple A P C s t x) w K hK
  refine ⟨orders, B, hB, fun f => ?_⟩
  apply (ContinuousMap.norm_le _ (mul_nonneg B.coe_nonneg (apply_nonneg _ _))).mpr
  intro g
  exact hb f g.val g.property

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
