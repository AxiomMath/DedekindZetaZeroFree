module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RestrictedTensorProduct
public import DedekindZetaZeroFree.Theta.Unfolding.TensorProducts.CompactSlotInsertion

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField KPGlobalTorusFiniteStages TensorActionSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)

theorem rawCoreInsertion_expanded (s t : RestrictedTensorSimple.Level (bad A P C))
    (hst : s ≤ t) (x : RestrictedTensorSimple.Stage (Plus A P C) s.val) (g : Raw A)
    (ht : ∀ p, p ∉ t.val → localValue A P C p (g p) (plusReference A P C p) = reference A P C p) :
    rawCoreInsertion A P C (RestrictedTensorSimple.stageInclusion _ (plusReference A P C)
      (bad A P C) s x) g =
      rawStageValue A P C t g
        (RestrictedTensorSimple.insert (Plus A P C) (plusReference A P C) s.val t.val hst x) := by
  have he : RestrictedTensorSimple.stageInclusion (Plus A P C) (plusReference A P C)
      (bad A P C) s x = RestrictedTensorSimple.stageInclusion (Plus A P C) (plusReference A P C)
        (bad A P C) t
        (RestrictedTensorSimple.insert (Plus A P C) (plusReference A P C) s.val t.val hst x) :=
    Module.DirectLimit.of_f.symm
  rw [he, rawCoreInsertion_stage A P C t _ g ht]

theorem rawCoreInsertion_stage_compact (s : RestrictedTensorSimple.Level (bad A P C))
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (k : KPCplxCharacterHaar.ComplexSU2)
    (x : RestrictedTensorSimple.Stage (Plus A P C) s.val) (g : Raw A) :
    rawCoreInsertion A P C (RestrictedTensorSimple.stageInclusion _ (plusReference A P C)
      (bad A P C) s (compactSlot A P C s.val w hw k x)) g =
    rawCoreInsertion A P C (RestrictedTensorSimple.stageInclusion _ (plusReference A P C)
      (bad A P C) s x)
      (g * KPAdelicCoverRestrictedProduct.localToRestricted F A.zeta12
        A.primitive_zeta12 (Sum.inl w) (literalLocalCompact A w k)) := by
  obtain ⟨u,hu⟩ := exists_reference_stage A P C g
  let t : RestrictedTensorSimple.Level (bad A P C) :=
    ⟨s.val ∪ u.val, s.property.trans Finset.subset_union_left⟩
  have hst : s ≤ t := Finset.subset_union_left
  have ht : ∀ p, p ∉ t.val → localValue A P C p (g p) (plusReference A P C p) = reference A P C p :=
    fun p hp => hu p (fun h => hp (Finset.mem_union_right _ h))
  have ht' : ∀ p, p ∉ t.val → localValue A P C p
      ((g * KPAdelicCoverRestrictedProduct.localToRestricted F A.zeta12
        A.primitive_zeta12 (Sum.inl w) (literalLocalCompact A w k)) p)
      (plusReference A P C p) = reference A P C p := by
    intro p hp
    have hne : p ≠ Sum.inl w := fun h => hp (h ▸ hst hw)
    simp only [RestrictedProduct.mul_apply, KPAdelicCoverRestrictedProduct.localToRestricted,
      RestrictedProduct.mulSingleMonoidHom_apply, RestrictedProduct.coe_mulSingle_apply,
      Pi.mulSingle_eq_of_ne hne, mul_one]
    exact ht p hp
  rw [rawCoreInsertion_expanded A P C s t hst _ g ht,
    rawCoreInsertion_expanded A P C s t hst _ _ ht',
    compactSlot_insert A P C (plusReference A P C) s.val t.val hst w hw k x]
  exact rawStageInsertion_compact A P C t w (hst hw) k _ g

theorem arch_mem_stage (s : RestrictedTensorSimple.Level (bad A P C)) (w : InfinitePlace F) :
    Sum.inl w ∈ s.val := s.property (by simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad])

def coreCompactSlot (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2) :
    Module.End ℂ (RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C)) :=
  Module.DirectLimit.lift ℂ (RestrictedTensorSimple.Level (bad A P C))
    (fun s => RestrictedTensorSimple.Stage (Plus A P C) s.val)
    (RestrictedTensorSimple.transition (Plus A P C) (plusReference A P C) (bad A P C))
    (fun s => (RestrictedTensorSimple.stageInclusion (Plus A P C) (plusReference A P C)
      (bad A P C) s).comp (compactSlot A P C s.val w (arch_mem_stage A P C s w) k))
    (by
      intro s t hst x
      change RestrictedTensorSimple.stageInclusion (Plus A P C) (plusReference A P C)
        (bad A P C) t (compactSlot A P C t.val w _ k
          (RestrictedTensorSimple.insert _ _ s.val t.val hst x)) = _
      rw [← compactSlot_insert A P C (plusReference A P C) s.val t.val hst w
        (arch_mem_stage A P C s w) k x]
      exact Module.DirectLimit.of_f)

@[simp] theorem coreCompactSlot_stage (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2)
    (s : RestrictedTensorSimple.Level (bad A P C))
    (x : RestrictedTensorSimple.Stage (Plus A P C) s.val) :
    coreCompactSlot A P C w k
      (RestrictedTensorSimple.stageInclusion _ (plusReference A P C) (bad A P C) s x) =
    RestrictedTensorSimple.stageInclusion _ (plusReference A P C) (bad A P C) s
      (compactSlot A P C s.val w (arch_mem_stage A P C s w) k x) := by
  unfold coreCompactSlot RestrictedTensorSimple.stageInclusion
  rw [Module.DirectLimit.lift_of, LinearMap.comp_apply]

theorem rawCoreInsertion_compact (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2)
    (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C)) (g : Raw A) :
    rawCoreInsertion A P C (coreCompactSlot A P C w k x) g =
    rawCoreInsertion A P C x
      (g * KPAdelicCoverRestrictedProduct.localToRestricted F A.zeta12
        A.primitive_zeta12 (Sum.inl w) (literalLocalCompact A w k)) := by
  letI : Nonempty (RestrictedTensorSimple.Level (bad A P C)) := ⟨⟨bad A P C, le_rfl⟩⟩
  induction x using Module.DirectLimit.induction_on with
  | ih s x =>
    change rawCoreInsertion A P C (coreCompactSlot A P C w k
      (RestrictedTensorSimple.stageInclusion _ _ _ s x)) g = _
    rw [coreCompactSlot_stage]
    exact rawCoreInsertion_stage_compact A P C s w (arch_mem_stage A P C s w) k x g

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
