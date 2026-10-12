module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.FiniteHarishChandraFamilies
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RestrictedTensorProduct
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.ReferenceSectionNormalization

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option quotPrecheck false
namespace DedekindZetaZeroFree.FourierContinuation.CurrentFixedSlices
open KPLocalPrincipalSeries KPLocalStoneVonNeumann
open NativeScalarMixedTensorGeneration KPLiteralScalarHCCompactOrbit
open KPLiteralTensor.KernelAndHCRange.PointwiseKernel
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductCovariantSlices renaming contraction → contraction
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductCovariantSlices renaming contractionMultilinear → contractionMultilinear
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming normalized_reference → normalized_reference

section Contraction
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem evaluation_contraction (q : ι) (l : ∀ i, V i →ₗ[ℂ] ℂ)
    (e : V q →ₗ[ℂ] ℂ) (x : PiTensorProduct ℂ V) :
    tensorEvaluation (Function.update l q e) x = e (contraction q l x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, contraction, PiTensorProduct.lift.tprod,
      tensorEvaluation, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, contractionMultilinear, MultilinearMap.mk'_apply]
    congr 1
    rw [smul_eq_mul, ← Finset.mul_prod_erase _ _ (Finset.mem_univ q)]
    simp only [Function.update_self]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  | add x y hx hy => simp only [map_add, hx, hy]
end Contraction

variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "M" => CurrentFiniteFamily.nativeInducingData A P C

section Local
variable (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
local notation "B" => (C.canonical q).borel
local notation "L" => C.polarization q
local notation "Section" => sectionSpace B L .plus 0

def localScalar : Section →ₗ[ℂ]
    (KPLocalExceptionalConstruction.ActualCover F A.zeta12 A.primitive_zeta12 q → ℂ) where
  toFun f a := (f.val a).val 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem localScalar_recovery (f : Section)
    (t : KPLocalExceptionalConstruction.actualTorus F A.zeta12 A.primitive_zeta12 q)
    (g : KPLocalExceptionalConstruction.ActualCover F A.zeta12 A.primitive_zeta12 q) :
    (f.val g).val t = (deltaHalf B ((C.canonical q).borel.torus t))⁻¹ *
      localScalar A P C q f (((C.canonical q).borel.torus t).val * g) := by
  have h := f.property.1 ((C.canonical q).borel.torus t) g
  have hv := congrArg (fun v : InducedModule L => v.val 1) h
  change localScalar A P C q f (((C.canonical q).borel.torus t).val * g) =
    inducingScalar B 0 ((C.canonical q).borel.torus t) *
      (f.val g).val (1 * (C.canonical q).borel.retract ((C.canonical q).borel.torus t)) at hv
  rw [(C.canonical q).borel.retract_torus, one_mul] at hv
  simp only [inducingScalar, normPower, zero_mul, Complex.exp_zero, mul_one] at hv
  rw [hv, inv_mul_cancel_left₀]
  exact Complex.exp_ne_zero _

theorem localScalar_injective : Function.Injective (localScalar A P C q) := by
  intro f g h
  apply Subtype.ext
  funext a
  apply Subtype.ext
  funext t
  rw [localScalar_recovery A P C q, localScalar_recovery A P C q, h]

theorem canonical_fixed_section_factorization (hq : q ∉ C.exceptional)
    (f : Section)
    (hf : ∀ k : (C.canonical q).iwasawa.compact.toOpenSubgroup,
      ∀ a, (f.val (a * k.val)).val 1 = (f.val a).val 1) :
    f = (f.val 1).val 1 • LiteralSource.plusReference A P C (Sum.inr q) := by
  apply KPLiteralScalarCanonicalReferenceComparison.fixed_section_eq_identity_scalar
    B L (C.canonical q).iwasawa (C.unramified q hq)
  · intro k
    apply localScalar_injective A P C q
    funext a
    exact hf k a
  · exact LiteralSource.plusReference_fixed A P C q hq
  · simp only [LiteralSource.plusReference, dite_eq_left hq]
    rw [(normalized_reference A P C q hq).choose_spec.2]
    simp only [KPGlobalTorusFiniteStages.localReference, map_one, Subgroup.one_mem, dite_true]
    change (((C.polarization q).ωL 1 : ℂˣ) : ℂ) = 1
    rw [map_one, Units.val_one]
end Local

theorem finite_plus_scalar_injective (q : KPFinitePlace F)
    (f g : SourceReconstruction.localPlus F A.zeta12 A.primitive_zeta12 M (Sum.inr q))
    (he : ∀ a, (f.val a).val 1 = (g.val a).val 1) : f = g :=
  localScalar_injective A P C q (funext he)

section Tensor
variable (U : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
local instance (j : InfinitePlace F ⊕ U) :
    AddCommGroup (mixedSource F A.zeta12 A.primitive_zeta12 M U j) := by
  cases j with
  | inl w => dsimp [mixedSource]; infer_instance
  | inr q => exact SourceReconstruction.localPlusAdd F A.zeta12 A.primitive_zeta12 M (Sum.inr q.val)
local instance (j : InfinitePlace F ⊕ U) :
    Module ℂ (mixedSource F A.zeta12 A.primitive_zeta12 M U j) := by
  cases j with
  | inl w => dsimp [mixedSource]; infer_instance
  | inr q => exact SourceReconstruction.localPlusModule F A.zeta12 A.primitive_zeta12 M (Sum.inr q.val)

def slotEvaluation (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
    (g : KPLiteralScalarHCFiniteProduct.FiniteProductCover F A.zeta12 A.primitive_zeta12 U)
    (j : InfinitePlace F ⊕ U) : mixedSource F A.zeta12 A.primitive_zeta12 M U j →ₗ[ℂ] ℂ := by
  cases j with
  | inl w => exact { toFun := fun x => x.val (m w), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  | inr q => exact { toFun := fun x => (x.val (g q)).val 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem allSlotEvaluation_eq_product
    (x : PiTensorProduct ℂ (mixedSource (ι := InfinitePlace F) F A.zeta12 A.primitive_zeta12 M U))
    (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
    (g : KPLiteralScalarHCFiniteProduct.FiniteProductCover F A.zeta12 A.primitive_zeta12 U) :
    allSlotEvaluation F A.zeta12 A.primitive_zeta12 M U x m g =
      tensorEvaluation (slotEvaluation A P C U m g) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, Pi.smul_apply]
    congr 1
    rw [allSlotEvaluation_pure]
    simp only [tensorEvaluation, PiTensorProduct.lift.tprod,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      Fintype.prod_sum_type]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem allSlotEvaluation_finite_slice
    (x : PiTensorProduct ℂ (mixedSource (ι := InfinitePlace F) F A.zeta12 A.primitive_zeta12 M U))
    (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
    (g : KPLiteralScalarHCFiniteProduct.FiniteProductCover F A.zeta12 A.primitive_zeta12 U)
    (q : U) :
    ∃ v : SourceReconstruction.localPlus F A.zeta12 A.primitive_zeta12 M (Sum.inr q.val),
      ∀ a, (v.val a).val 1 =
        allSlotEvaluation F A.zeta12 A.primitive_zeta12 M U x m (Function.update g q a) := by
  refine ⟨contraction (Sum.inr q) (slotEvaluation A P C U m g) x, ?_⟩
  intro a
  rw [allSlotEvaluation_eq_product]
  have hl : slotEvaluation A P C U m (Function.update g q a) =
    Function.update (slotEvaluation A P C U m g) (Sum.inr q)
      (slotEvaluation A P C U m (Function.update g q a) (Sum.inr q)) := by
    funext j
    cases j with
    | inl w => simp [slotEvaluation]
    | inr r =>
      by_cases hr : r = q
      · subst r; simp
      · have hs : (Sum.inr r : InfinitePlace F ⊕ U) ≠ Sum.inr q := fun h => hr (Sum.inr.inj h)
        simp [slotEvaluation, Function.update_of_ne hr, Function.update_of_ne hs]
  rw [hl, evaluation_contraction]
  simp only [slotEvaluation, Function.update_self, LinearMap.coe_mk, AddHom.coe_mk]
end Tensor
end DedekindZetaZeroFree.FourierContinuation.CurrentFixedSlices

end
