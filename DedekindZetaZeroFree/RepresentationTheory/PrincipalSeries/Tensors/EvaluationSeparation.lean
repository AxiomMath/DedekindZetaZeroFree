module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.FixedSliceFactorization

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option quotPrecheck false
namespace DedekindZetaZeroFree.FourierContinuation.CurrentReferenceFactorization
open FourierContinuation.CurrentFixedSlices NativeScalarMixedTensorGeneration
open KPLiteralScalarHCFiniteProduct
open KPLiteralTensor.KernelAndHCRange.PointwiseKernel
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)
variable (U : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
local notation "M" => FourierContinuation.CurrentFiniteFamily.nativeInducingData A P C
local notation "Source" => mixedSource (ι := InfinitePlace F) F A.zeta12 A.primitive_zeta12 M U
local notation "Eval" => allSlotEvaluation F A.zeta12 A.primitive_zeta12 M U
local instance (j : InfinitePlace F ⊕ U) : AddCommGroup (Source j) := by
  cases j with
  | inl w => dsimp [mixedSource]; infer_instance
  | inr q => exact FourierContinuation.SourceReconstruction.localPlusAdd F A.zeta12 A.primitive_zeta12 M (Sum.inr q.val)
local instance (j : InfinitePlace F ⊕ U) : Module ℂ (Source j) := by
  cases j with
  | inl w => dsimp [mixedSource]; infer_instance
  | inr q => exact FourierContinuation.SourceReconstruction.localPlusModule F A.zeta12 A.primitive_zeta12 M (Sum.inr q.val)

theorem allSlotEvaluation_fixed_reference
    (q : U) (hq : q.val ∉ C.exceptional)
    (x : PiTensorProduct ℂ Source)
    (hfix : ∀ (k : (C.canonical q.val).iwasawa.compact.toOpenSubgroup)
      (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
      (a : FiniteProductCover F A.zeta12 A.primitive_zeta12 U),
      Eval x m (Function.update a q (a q * k.val)) = Eval x m a)
    (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
    (a : FiniteProductCover F A.zeta12 A.primitive_zeta12 U) :
    Eval x m a = ((FourierContinuation.LiteralSource.plusReference A P C (Sum.inr q.val)).val (a q)).val 1 *
      Eval x m (Function.update a q 1) := by
  obtain ⟨v, hv⟩ := allSlotEvaluation_finite_slice A P C U x m a q
  have hf : ∀ (k : (C.canonical q.val).iwasawa.compact.toOpenSubgroup) b,
      (v.val (b * k.val)).val 1 = (v.val b).val 1 := by
    intro k b
    rw [hv, hv]
    simpa only [Function.update_self, Function.update_idem] using
      (hfix k m (Function.update a q b))
  have he := canonical_fixed_section_factorization A P C q.val hq v hf
  have hval := congrArg (fun w => (w.val (a q)).val 1) he
  change (v.val (a q)).val 1 = (v.val 1).val 1 *
    ((FourierContinuation.LiteralSource.plusReference A P C (Sum.inr q.val)).val (a q)).val 1 at hval
  rw [hv, hv] at hval
  simpa only [Function.update_eq_self, mul_comm] using hval

 abbrev Arguments : InfinitePlace F ⊕ U → Type
  | Sum.inl _ => KPCplxCharacterHaar.ComplexGL2
  | Sum.inr q => KPLocalExceptionalConstruction.ActualCover F A.zeta12 A.primitive_zeta12 q.val

 def detector (j : InfinitePlace F ⊕ U) (a : Arguments A U j) : Source j →ₗ[ℂ] ℂ := by
  cases j with
  | inl w => exact { toFun := fun v => v.val a, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  | inr q => exact { toFun := fun v => (v.val a).val 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem allSlotEvaluation_injective : Function.Injective (allSlotEvaluation (ι := InfinitePlace F) F A.zeta12 A.primitive_zeta12 M U) := by
  intro x y he
  apply sub_eq_zero.mp
  apply tensor_evaluations_separate (detector A P C U)
  · intro j v hv
    cases j with
    | inl w =>
      apply Subtype.ext
      apply Subtype.ext
      funext a
      exact hv a
    | inr q =>
      apply finite_plus_scalar_injective A P C q.val
      intro a
      exact hv a
  · intro a
    let m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 := fun w => a (Sum.inl w)
    let g : FiniteProductCover F A.zeta12 A.primitive_zeta12 U := fun q => a (Sum.inr q)
    have hl : (fun j => detector A P C U j (a j)) = slotEvaluation A P C U m g := by
      funext j
      cases j <;> rfl
    rw [hl, ← allSlotEvaluation_eq_product]
    simp only [map_sub, Pi.sub_apply, he, sub_self]

end DedekindZetaZeroFree.FourierContinuation.CurrentReferenceFactorization

end
