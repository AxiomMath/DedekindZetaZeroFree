module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.HarishChandraReferenceTail

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
set_option quotPrecheck false
namespace DedekindZetaZeroFree.FourierContinuation.CurrentTransitionEvaluation
open FourierContinuation.CurrentNativeStage NativeScalarMixedTensorGeneration
open KPLiteralScalarHCFiniteProduct
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "M" => FourierContinuation.CurrentFiniteFamily.nativeInducingData A P C
local notation "V" => FourierContinuation.LiteralSource.Plus A P C
local notation "bad" => FourierContinuation.LiteralSource.bad A P C
local instance (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (j : InfinitePlace F ⊕ T) : AddCommGroup (mixedSource F A.zeta12 A.primitive_zeta12 M T j) := by
  cases j with
  | inl w => dsimp [mixedSource]; infer_instance
  | inr q => exact FourierContinuation.SourceReconstruction.localPlusAdd F A.zeta12 A.primitive_zeta12 M (Sum.inr q.val)
local instance (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (j : InfinitePlace F ⊕ T) : Module ℂ (mixedSource F A.zeta12 A.primitive_zeta12 M T j) := by
  cases j with
  | inl w => dsimp [mixedSource]; infer_instance
  | inr q => exact FourierContinuation.SourceReconstruction.localPlusModule F A.zeta12 A.primitive_zeta12 M (Sum.inr q.val)
variable (T U : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
variable (hT : C.exceptional ⊆ T) (hU : C.exceptional ⊆ U) (hTU : T ⊆ U)

include hTU in
theorem stageSubset : fullStage A P C T hT ≤ fullStage A P C U hU := by
  intro j hj
  cases j with
  | inl w => simp [fullStage]
  | inr q => simpa [fullStage] using hTU (by simpa [fullStage] using hj)

def nativeTransition :
    PiTensorProduct ℂ (mixedSource (ι := InfinitePlace F) F A.zeta12 A.primitive_zeta12 M T) →ₗ[ℂ]
    PiTensorProduct ℂ (mixedSource (ι := InfinitePlace F) F A.zeta12 A.primitive_zeta12 M U) :=
  (nativeStageEquiv A P C U hU).toLinearMap.comp
    ((RestrictedTensorSimple.transition V (FourierContinuation.LiteralSource.plusReference A P C) bad
      (fullStage A P C T hT) (fullStage A P C U hU) (stageSubset A P C T U hT hU hTU)).comp
        (nativeStageEquiv A P C T hT).symm.toLinearMap)

def enlargedComponents
    (x : ∀ j : InfinitePlace F ⊕ T, mixedSource F A.zeta12 A.primitive_zeta12 M T j) :
    ∀ j : InfinitePlace F ⊕ U, mixedSource F A.zeta12 A.primitive_zeta12 M U j
  | Sum.inl w => x (Sum.inl w)
  | Sum.inr q => if h : q.val ∈ T then x (Sum.inr ⟨q.val, h⟩) else FourierContinuation.LiteralSource.plusReference A P C (Sum.inr q.val)

theorem nativeTransition_pure
    (x : ∀ j : InfinitePlace F ⊕ T, mixedSource F A.zeta12 A.primitive_zeta12 M T j) :
    nativeTransition A P C T U hT hU hTU (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (enlargedComponents A P C T U x) := by
  have he := congrArg (nativeStageEquiv A P C T hT).symm
    (nativeStageEquiv_pure A P C T hT x)
  simp only [LinearEquiv.symm_apply_apply] at he
  dsimp only [nativeTransition, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← he]
  rw [RestrictedTensorSimple.transition, RestrictedTensorSimple.insert_pure]
  have hv : (fun j : (fullStage A P C U hU).val =>
      if h : j.val ∈ (fullStage A P C T hT).val then
        stageComponents A P C T hT x ⟨j.val, h⟩ else FourierContinuation.LiteralSource.plusReference A P C j.val) =
      stageComponents A P C U hU (enlargedComponents A P C T U x) := by
    funext j
    rcases j with ⟨w | q, hj⟩
    · simp [fullStage, stageComponents, enlargedComponents]
    · by_cases hq : q ∈ T <;> simp [fullStage, stageComponents, enlargedComponents, hq]
  convert (congrArg (nativeStageEquiv A P C U hU)
    (congrArg (PiTensorProduct.tprod ℂ) hv)).trans
      (nativeStageEquiv_pure A P C U hU (enlargedComponents A P C T U x)) using 1
  congr 2
  funext j
  split <;> rfl
 def oldFiniteIndex : (Finset.univ.filter (fun q : U => q.val ∈ T)) ≃ T where
  toFun q := ⟨q.val.val, (Finset.mem_filter.mp q.property).2⟩
  invFun q := ⟨⟨q.val, hTU q.property⟩, by simp [q.property]⟩
  left_inv q := by cases q; rfl
  right_inv q := rfl

theorem nativeTransition_evaluation
    (x : PiTensorProduct ℂ (mixedSource (ι := InfinitePlace F) F A.zeta12 A.primitive_zeta12 M T))
    (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
    (a : FiniteProductCover F A.zeta12 A.primitive_zeta12 U) :
    allSlotEvaluation F A.zeta12 A.primitive_zeta12 M U
      (nativeTransition A P C T U hT hU hTU x) m a =
      (∏ q : U with q.val ∉ T, ((FourierContinuation.LiteralSource.plusReference A P C (Sum.inr q.val)).val (a q)).val 1) *
        allSlotEvaluation F A.zeta12 A.primitive_zeta12 M T x m
          (fun q => a ⟨q.val, hTU q.property⟩) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, nativeTransition_pure,
      allSlotEvaluation_pure]
    have hp :
        (∏ q : U, (((enlargedComponents A P C T U x) (Sum.inr q)).val (a q)).val 1) =
        (∏ q : T, ((x (Sum.inr q)).val (a ⟨q.val, hTU q.property⟩)).val 1) *
        (∏ q : U with q.val ∉ T, ((FourierContinuation.LiteralSource.plusReference A P C (Sum.inr q.val)).val (a q)).val 1) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun q : U => q.val ∈ T)]
      congr 1
      · rw [← Finset.prod_coe_sort]
        apply Fintype.prod_equiv (oldFiniteIndex T U hTU)
        intro q
        simp [oldFiniteIndex, enlargedComponents, (Finset.mem_filter.mp q.property).2]
      · apply Finset.prod_congr rfl
        intro q hq
        simp [enlargedComponents, (Finset.mem_filter.mp hq).2]
    rw [hp]
    have ha : (∏ w : InfinitePlace F, (((enlargedComponents A P C T U x) (Sum.inl w)).val (m w))) =
        ∏ w : InfinitePlace F, ((x (Sum.inl w)).val (m w)) := rfl
    rw [ha]
    ring
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy, mul_add]
end DedekindZetaZeroFree.FourierContinuation.CurrentTransitionEvaluation

end
