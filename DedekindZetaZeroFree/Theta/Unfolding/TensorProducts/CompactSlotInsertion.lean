module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalTensorEvaluation
public import DedekindZetaZeroFree.Theta.Unfolding.TensorProducts.ProductCompactCovariance

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

theorem localValue_compact (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2)
    (f : Plus A P C (Sum.inl w))
    (g : KPLocalCover.CubicGL2Raw F A.zeta12 A.primitive_zeta12 (Sum.inl w)) :
    localValue A P C (Sum.inl w) g (harmonicSourceAction k f) =
      localValue A P C (Sum.inl w) (g * literalLocalCompact A w k) f :=
  literalLocalValue_compact A w k f g

def compactSlot (s : Finset (KPHilbert.Place F)) (w : InfinitePlace F)
    (hw : Sum.inl w ∈ s) (k : KPCplxCharacterHaar.ComplexSU2) :
    Module.End ℂ (RestrictedTensorSimple.Stage (Plus A P C) s) :=
  PiTensorProduct.map (Function.update
    (fun j : s => LinearMap.id (R := ℂ) (M := Plus A P C j.val))
    ⟨Sum.inl w, hw⟩ (harmonicSourceAction k))

theorem compactSlot_pure (s : Finset (KPHilbert.Place F)) (w : InfinitePlace F)
    (hw : Sum.inl w ∈ s) (k : KPCplxCharacterHaar.ComplexSU2)
    (x : ∀ j : s, Plus A P C j.val) :
    compactSlot A P C s w hw k (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w,hw⟩
        (harmonicSourceAction k (x ⟨Sum.inl w,hw⟩))) := by
  rw [compactSlot, PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases hj : j = ⟨Sum.inl w,hw⟩
  · subst j; simp
  · simp [Function.update_of_ne hj]

theorem rawStageInsertion_compact_pure (s : RestrictedTensorSimple.Level (bad A P C))
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (k : KPCplxCharacterHaar.ComplexSU2) (x : ∀ j : s.val, Plus A P C j.val)
    (g : Raw A) :
    rawStageInsertion A P C s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w,hw⟩
        (harmonicSourceAction k (x ⟨Sum.inl w,hw⟩)))) g =
    rawStageInsertion A P C s (PiTensorProduct.tprod ℂ x)
      (g * KPAdelicCoverRestrictedProduct.localToRestricted F A.zeta12
        A.primitive_zeta12 (Sum.inl w) (literalLocalCompact A w k)) := by
  rw [rawStageInsertion_pure, rawStageInsertion_pure]
  apply congrArg (fun y => (comparison A P C
    (RestrictedTensorSimple.stageInclusion (Fiber A P C) (reference A P C)
      (bad A P C) s (PiTensorProduct.tprod ℂ y))).val.val 1)
  funext j
  by_cases hj : j = ⟨Sum.inl w,hw⟩
  · subst j
    simp only [Function.update_self, RestrictedProduct.mul_apply,
      KPAdelicCoverRestrictedProduct.localToRestricted,
      RestrictedProduct.mulSingleMonoidHom_apply, RestrictedProduct.coe_mulSingle_apply,
      Pi.mulSingle_eq_same]
    exact localValue_compact A P C w k _ _
  · have hv : j.val ≠ Sum.inl w := fun h => hj (Subtype.ext h)
    simp only [Function.update_of_ne hj, RestrictedProduct.mul_apply,
      KPAdelicCoverRestrictedProduct.localToRestricted,
      RestrictedProduct.mulSingleMonoidHom_apply, RestrictedProduct.coe_mulSingle_apply,
      Pi.mulSingle_eq_of_ne hv, mul_one]

theorem rawStageInsertion_compact (s : RestrictedTensorSimple.Level (bad A P C))
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (k : KPCplxCharacterHaar.ComplexSU2)
    (x : RestrictedTensorSimple.Stage (Plus A P C) s.val) (g : Raw A) :
    rawStageInsertion A P C s (compactSlot A P C s.val w hw k x) g =
    rawStageInsertion A P C s x
      (g * KPAdelicCoverRestrictedProduct.localToRestricted F A.zeta12
        A.primitive_zeta12 (Sum.inl w) (literalLocalCompact A w k)) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, Pi.smul_apply, compactSlot_pure, rawStageInsertion_compact_pure]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem compactSlot_insert (r : ∀ p, Plus A P C p)
    (s t : Finset (KPHilbert.Place F)) (hst : s ⊆ t)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s) (k : KPCplxCharacterHaar.ComplexSU2)
    (x : RestrictedTensorSimple.Stage (Plus A P C) s) :
    RestrictedTensorSimple.insert (Plus A P C) r s t hst (compactSlot A P C s w hw k x) =
      compactSlot A P C t w (hst hw) k
        (RestrictedTensorSimple.insert (Plus A P C) r s t hst x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, compactSlot_pure, RestrictedTensorSimple.insert_pure]
    congr 1
    apply congrArg (PiTensorProduct.tprod ℂ)
    funext j
    by_cases hj : j.val = Sum.inl w
    · have hje : j = (⟨Sum.inl w,hst hw⟩ : t) := Subtype.ext hj
      subst j
      simp only [Function.update_self, dite_eq_left hw]
    · have hje : j ≠ (⟨Sum.inl w,hst hw⟩ : t) := fun h => hj (congrArg Subtype.val h)
      rw [Function.update_of_ne hje]
      split_ifs with h
      · have hjs : (⟨j.val,h⟩ : s) ≠ ⟨Sum.inl w,hw⟩ := fun h => hj (congrArg Subtype.val h)
        rw [Function.update_of_ne hjs]
      · rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
