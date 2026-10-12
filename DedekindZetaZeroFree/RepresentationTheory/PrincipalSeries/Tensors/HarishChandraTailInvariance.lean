module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.FiniteStageInsertion
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.EvaluationSeparation
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.StandardCompactTailEvaluation

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
namespace DedekindZetaZeroFree.FourierContinuation.CurrentTailFixation
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralScalarHCExtraction
open KPLiteralScalarHCFiniteInsertion KPLiteralScalarHCFiniteProduct KPLiteralScalarHCCompactOrbit
open NativeScalarMixedTensorGeneration KPLiteralScalarHCSliceCharts
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "M" => FourierContinuation.CurrentFiniteFamily.nativeInducingData A P C
local notation "Raw" => RestrictedCover F A.zeta12 A.primitive_zeta12
variable (K : Subgroup (KPLiteralRaw.G F A.zeta12 A.primitive_zeta12))
variable (hK : IwasawaCompact F A.zeta12 A.primitive_zeta12 K)
variable (f : Flat F A.zeta12 A.primitive_zeta12 K)
variable (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
variable (hT : C.exceptional ⊆ T) (hbad : ∀ q, Bad F q → q ∈ T)
variable (htail : ∀ (r : RestrictedCover F A.zeta12 A.primitive_zeta12)
    (hi : ∀ w : InfinitePlace F, r (Sum.inl w) = 1)
    (hin : ∀ q ∈ T, KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) (r (Sum.inr q)) = 1)
    (hout : ∀ q, q ∉ T → KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) (r (Sum.inr q)) ∈ pglCompact F A.zeta12 A.primitive_zeta12 (Sum.inr q))
    (g : KPLiteralRaw.G F A.zeta12 A.primitive_zeta12),
    (productHCSection F A.zeta12 A.primitive_zeta12 K hK P f).val.val
      (g * scalarQuotient F A.zeta12 A.primitive_zeta12 (amalgamation F A.zeta12 A.primitive_zeta12 r)) =
    (productHCSection F A.zeta12 A.primitive_zeta12 K hK P f).val.val g)

include hT hbad htail in

theorem original_HC_added_slot_fixed
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hq : q ∉ T)
    (k : (C.canonical q).iwasawa.compact.toOpenSubgroup)
    (g : KPLiteralRaw.G F A.zeta12 A.primitive_zeta12) :
    productHCScalar F A.zeta12 A.primitive_zeta12 K hK P f
      (g * (finiteInsertion F A.zeta12 A.primitive_zeta12 q k.val).val) =
    productHCScalar F A.zeta12 A.primitive_zeta12 K hK P f g := by
  obtain ⟨ht, hc⟩ := C.actual_compact q (fun h => hq (hT h))
  have hk : k.val ∈ (KPLocalExceptionalConstruction.actualGoodCompactSplit F A.zeta12 A.primitive_zeta12 q ht).range := by
    rw [← hc]
    exact k.property
  obtain ⟨k₀, hk₀⟩ := hk
  let a := KPGoodCompactSplitting.kStar F A.zeta12 A.primitive_zeta12 q ht k₀
  let r := localToRestricted F A.zeta12 A.primitive_zeta12 (Sum.inr q) a
  have hquot : KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) a = k.val := hk₀
  have he := htail r (by intro w; simp [r, localToRestricted, RestrictedProduct.coe_mulSingle_apply])
    (by
      intro p hp
      have hn : p ≠ q := by intro h; subst p; exact hq hp
      simp [r, localToRestricted, RestrictedProduct.coe_mulSingle_apply, hn])
    (by
      intro p hp
      by_cases he : p = q
      · subst p
        have hr : r (Sum.inr q) = a := by simp [r, localToRestricted]
        rw [hr, hquot]
        change k.val ∈ (finiteCompact F A.zeta12 A.primitive_zeta12 q).map _
        simp only [finiteCompact, dite_eq_right (fun h => hq (hbad q h))]
        rw [← MonoidHom.range_comp, ← KPLocalExceptionalConstruction.actualGoodCompactSplit, ← hc]
        exact k.property
      · simp [r, localToRestricted, RestrictedProduct.coe_mulSingle_apply, he]) g
  have hi : scalarQuotient F A.zeta12 A.primitive_zeta12 (amalgamation F A.zeta12 A.primitive_zeta12 r) =
      (finiteInsertion F A.zeta12 A.primitive_zeta12 q k.val).val := by
    rw [finiteInsertion_value, ← hquot, finiteGroupInsertion_raw]
    rfl
  rw [hi] at he
  exact congrArg (fun v => v.val.val 1) he
local instance (U : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (j : InfinitePlace F ⊕ U) : AddCommGroup (mixedSource F A.zeta12 A.primitive_zeta12 M U j) := by
  cases j with
  | inl w => dsimp [mixedSource]; infer_instance
  | inr q => exact FourierContinuation.SourceReconstruction.localPlusAdd F A.zeta12 A.primitive_zeta12 M (Sum.inr q.val)
local instance (U : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (j : InfinitePlace F ⊕ U) : Module ℂ (mixedSource F A.zeta12 A.primitive_zeta12 M U j) := by
  cases j with
  | inl w => dsimp [mixedSource]; infer_instance
  | inr q => exact FourierContinuation.SourceReconstruction.localPlusModule F A.zeta12 A.primitive_zeta12 M (Sum.inr q.val)
include hT hbad htail in

theorem HC_tensor_added_slot_fixed
    (U : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (x : PiTensorProduct ℂ (mixedSource (ι := InfinitePlace F) F A.zeta12 A.primitive_zeta12 M U))
    (hx : ∀ m a, allSlotEvaluation F A.zeta12 A.primitive_zeta12 M U x m a =
      productHCScalar F A.zeta12 A.primitive_zeta12 K hK P f
        ((finiteProductInsertion F A.zeta12 A.primitive_zeta12 U a).val * archMatrixInsertion F A.zeta12 A.primitive_zeta12 m))
    (q : U) (hq : q.val ∉ T)
    (k : (C.canonical q.val).iwasawa.compact.toOpenSubgroup)
    (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
    (a : FiniteProductCover F A.zeta12 A.primitive_zeta12 U) :
    allSlotEvaluation F A.zeta12 A.primitive_zeta12 M U x m (Function.update a q (a q * k.val)) =
    allSlotEvaluation F A.zeta12 A.primitive_zeta12 M U x m a := by
  have ha : Function.update a q (a q * k.val) = a * Pi.mulSingle q k.val := by
    funext j
    by_cases hj : j = q
    · subst j; simp
    · simp [Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hj]
  rw [ha, hx, hx, map_mul, finiteProductInsertion_single]
  change productHCScalar F A.zeta12 A.primitive_zeta12 K hK P f
    (((finiteProductInsertion F A.zeta12 A.primitive_zeta12 U a).val *
       (finiteInsertion F A.zeta12 A.primitive_zeta12 q.val k.val).val) * _) = _
  rw [mul_assoc, ← (archMatrixInsertion_commutes_finite F A.zeta12 A.primitive_zeta12 m
    (finiteInsertion F A.zeta12 A.primitive_zeta12 q.val k.val)).eq, ← mul_assoc]
  exact original_HC_added_slot_fixed A P C K hK f T hT hbad htail q.val hq k _

end DedekindZetaZeroFree.FourierContinuation.CurrentTailFixation

end
