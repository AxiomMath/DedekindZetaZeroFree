module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.NegativeSlotTensorEvaluation
public import DedekindZetaZeroFree.Adeles.Approximation.CompactReferenceTails
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicInverse

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts
open LiteralSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
local instance : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance : Module ℂ complexCore := Submodule.module complexCore
local instance : TopologicalSpace complexCore := instTopologicalSpaceSubtype
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)

def restrictedSlotTensor (s : RestrictedTensorSimple.Level (LiteralSource.bad A P C))
    (x : ∀ j : s.val, LiteralSource.Plus A P C j.val) (w : InfinitePlace F)
    (hw : Sum.inl w ∈ s.val) : complexCore →ₗ[ℂ]
      RestrictedTensorSimple.Core (LiteralSource.Plus A P C)
        (plusReference A P C) (LiteralSource.bad A P C) :=
  (RestrictedTensorSimple.stageInclusion _ _ _ s).comp
    (((PiTensorProduct.tprod ℂ (s := fun j : s.val => LiteralSource.Plus A P C j.val)).toLinearMap
      x ⟨Sum.inl w, hw⟩).comp
        harmonicInverse)

def enlargedTuple (s t : RestrictedTensorSimple.Level (LiteralSource.bad A P C))
    (x : ∀ j : s.val, LiteralSource.Plus A P C j.val) :
    ∀ j : t.val, LiteralSource.Plus A P C j.val :=
  fun j => if h : j.val ∈ s.val then x ⟨j.val, h⟩ else plusReference A P C j.val

theorem restrictedSlotTensor_enlarge
    (s t : RestrictedTensorSimple.Level (LiteralSource.bad A P C)) (hst : s ≤ t)
    (x : ∀ j : s.val, LiteralSource.Plus A P C j.val) (w : InfinitePlace F)
    (hw : Sum.inl w ∈ s.val) (v : complexCore) :
    restrictedSlotTensor A P C s x w hw v =
      restrictedSlotTensor A P C t (enlargedTuple A P C s t x) w (hst hw) v := by
  let f := harmonicInverse v
  have he : (fun j : t.val => if h : j.val ∈ s.val then
      Function.update x ⟨Sum.inl w, hw⟩ f ⟨j.val,h⟩ else plusReference A P C j.val) =
      Function.update (enlargedTuple A P C s t x) ⟨Sum.inl w, hst hw⟩ f := by
    funext j
    by_cases hj : j.val = Sum.inl w
    · have hj' : j = ⟨Sum.inl w, hst hw⟩ := Subtype.ext hj
      subst j
      simp [hw]
    · have hji : j ≠ (⟨Sum.inl w, hst hw⟩ : t.val) := fun h => hj (congrArg Subtype.val h)
      by_cases hs : j.val ∈ s.val
      · have hjs : (⟨j.val,hs⟩ : s.val) ≠ ⟨Sum.inl w,hw⟩ := fun h => hj (congrArg Subtype.val h)
        simp [hs, Function.update_of_ne hji, Function.update_of_ne hjs, enlargedTuple]
      · simp [hs, Function.update_of_ne hji, enlargedTuple]
  change RestrictedTensorSimple.stageInclusion _ _ _ s
    (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w,hw⟩ f)) =
    RestrictedTensorSimple.stageInclusion _ _ _ t
      (PiTensorProduct.tprod ℂ (Function.update (enlargedTuple A P C s t x) ⟨Sum.inl w,hst hw⟩ f))
  rw [← he]
  have hi := RestrictedTensorSimple.insert_pure (LiteralSource.Plus A P C)
    (plusReference A P C) s.val t.val hst (Function.update x ⟨Sum.inl w,hw⟩ f)
  have hi' := congrArg (RestrictedTensorSimple.stageInclusion (LiteralSource.Plus A P C)
    (plusReference A P C) (LiteralSource.bad A P C) t) hi
  have hf : RestrictedTensorSimple.stageInclusion (LiteralSource.Plus A P C)
      (plusReference A P C) (LiteralSource.bad A P C) t
      (RestrictedTensorSimple.transition (LiteralSource.Plus A P C) (plusReference A P C)
        (LiteralSource.bad A P C) s t hst
        (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w,hw⟩ f))) =
      RestrictedTensorSimple.stageInclusion (LiteralSource.Plus A P C)
        (plusReference A P C) (LiteralSource.bad A P C) s
        (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w,hw⟩ f)) :=
    Module.DirectLimit.of_f
  refine hf.symm.trans (hi'.trans ?_)
  congr 2
  funext j
  split_ifs <;> rfl

theorem restrictedSlot_raw_pin
    (s : RestrictedTensorSimple.Level (LiteralSource.bad A P C))
    (x : ∀ j : s.val, LiteralSource.Plus A P C j.val) (w : InfinitePlace F)
    (hw : Sum.inl w ∈ s.val) (g : LiteralSource.Raw A)
    (htail : ∀ v, v ∉ s.val → localValue A P C v (g v) (plusReference A P C v) =
      reference A P C v) (v : complexCore) :
    rawCoreInsertion A P C (restrictedSlotTensor A P C s x w hw v) g =
      CanonicalStageSlot.negative A P C s x g w v.val := by
  let f := harmonicInverse v
  change rawCoreInsertion A P C
    (RestrictedTensorSimple.stageInclusion _ _ _ s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w,hw⟩ f))) g = _
  rw [rawCoreInsertion_stage A P C s _ g htail]
  change rawStageInsertion A P C s (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w,hw⟩ f)) g = _
  rw [← CanonicalStageSlot.tensorValue_shared,
    ← CanonicalStageSlot.negative_tensor_pin A P C s x g w hw f,
    harmonicInverse_pin]

theorem restrictedSlot_raw_compact_bound
    (s : RestrictedTensorSimple.Level (LiteralSource.bad A P C))
    (x : ∀ j : s.val, LiteralSource.Plus A P C j.val) (w : InfinitePlace F)
    (hw : Sum.inl w ∈ s.val) (K : Set (LiteralSource.Raw A)) (hK : IsCompact K) :
    ∃ orders : Finset ℕ, ∃ B : ℝ≥0, B ≠ 0 ∧
      ∀ (v : complexCore) (g : LiteralSource.Raw A), g ∈ K →
        ‖rawCoreInsertion A P C (restrictedSlotTensor A P C s x w hw v) g‖ ≤
          B * (orders.sup coreSeminorm) v := by
  obtain ⟨t, hst, htail⟩ := exists_compact_reference_stage A P C s K hK
  obtain ⟨orders, B, hB, hb⟩ := CanonicalStageSlot.negative_raw_compact_bound
    A P C t (enlargedTuple A P C s t x) w K hK
  refine ⟨orders, B, hB, ?_⟩
  intro v g hg
  rw [restrictedSlotTensor_enlarge A P C s t hst x w hw v,
    restrictedSlot_raw_pin A P C t _ w (hst hw) g (htail g hg) v]
  have he : (orders.sup coreSeminorm) v =
      (orders.sup (chartSeminorm negativeParameter)) v.val := by
    change (orders.sup (SeminormFamily.comp (chartSeminorm negativeParameter) complexCore.subtype)) v = _
    rw [← SeminormFamily.finset_sup_comp, Seminorm.comp_apply]
    rfl
  simpa only [he] using hb v.val g hg

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
