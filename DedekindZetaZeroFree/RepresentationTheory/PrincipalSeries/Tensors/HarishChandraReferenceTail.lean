module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.InsertionEnlargement
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.FiniteReferenceProducts

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
namespace DedekindZetaZeroFree.FourierContinuation.CurrentReferenceTailFormula
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralScalarHCExtraction
open KPLiteralScalarHCFiniteProduct KPLiteralScalarHCCompactOrbit
open NativeScalarMixedTensorGeneration FourierContinuation.CurrentTailFixation
open FourierContinuation.CurrentReferenceFactorization FourierContinuation.CurrentReferenceProduct
open FourierContinuation.CurrentInsertionEnlargement
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "M" => FourierContinuation.CurrentFiniteFamily.nativeInducingData A P C
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

theorem HC_tensor_reference_tail_formula
    (K : Subgroup (KPLiteralRaw.G F A.zeta12 A.primitive_zeta12))
    (hK : IwasawaCompact F A.zeta12 A.primitive_zeta12 K)
    (f : Flat F A.zeta12 A.primitive_zeta12 K)
    (T U : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (hT : C.exceptional ⊆ T) (hTU : T ⊆ U) (hbad : ∀ q, Bad F q → q ∈ T)
    (htail : ∀ (r : RestrictedCover F A.zeta12 A.primitive_zeta12)
      (hi : ∀ w : InfinitePlace F, r (Sum.inl w) = 1)
      (hin : ∀ q ∈ T, KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) (r (Sum.inr q)) = 1)
      (hout : ∀ q, q ∉ T → KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) (r (Sum.inr q)) ∈ pglCompact F A.zeta12 A.primitive_zeta12 (Sum.inr q))
      (g : KPLiteralRaw.G F A.zeta12 A.primitive_zeta12),
      (productHCSection F A.zeta12 A.primitive_zeta12 K hK P f).val.val
        (g * scalarQuotient F A.zeta12 A.primitive_zeta12 (amalgamation F A.zeta12 A.primitive_zeta12 r)) =
      (productHCSection F A.zeta12 A.primitive_zeta12 K hK P f).val.val g)
    (xT : PiTensorProduct ℂ (mixedSource (ι := InfinitePlace F) F A.zeta12 A.primitive_zeta12 M T))
    (xU : PiTensorProduct ℂ (mixedSource (ι := InfinitePlace F) F A.zeta12 A.primitive_zeta12 M U))
    (hxT : ∀ m a, allSlotEvaluation F A.zeta12 A.primitive_zeta12 M T xT m a =
      productHCScalar F A.zeta12 A.primitive_zeta12 K hK P f
        ((finiteProductInsertion F A.zeta12 A.primitive_zeta12 T a).val * archMatrixInsertion F A.zeta12 A.primitive_zeta12 m))
    (hxU : ∀ m a, allSlotEvaluation F A.zeta12 A.primitive_zeta12 M U xU m a =
      productHCScalar F A.zeta12 A.primitive_zeta12 K hK P f
        ((finiteProductInsertion F A.zeta12 A.primitive_zeta12 U a).val * archMatrixInsertion F A.zeta12 A.primitive_zeta12 m))
    (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
    (a : FiniteProductCover F A.zeta12 A.primitive_zeta12 U) :
    allSlotEvaluation F A.zeta12 A.primitive_zeta12 M U xU m a =
      (∏ q : U with q.val ∉ T, ((FourierContinuation.LiteralSource.plusReference A P C (Sum.inr q.val)).val (a q)).val 1) *
        allSlotEvaluation F A.zeta12 A.primitive_zeta12 M T xT m
          (fun q => a ⟨q.val, hTU q.property⟩) := by
  let s := Finset.univ.filter (fun q : U => q.val ∉ T)
  let r : ∀ q : U, KPLocalExceptionalConstruction.ActualCover F A.zeta12 A.primitive_zeta12 q.val → ℂ :=
    fun q b => ((FourierContinuation.LiteralSource.plusReference A P C (Sum.inr q.val)).val b).val 1
  have hs : ∀ q ∈ s, ∀ g : FiniteProductCover F A.zeta12 A.primitive_zeta12 U,
      allSlotEvaluation F A.zeta12 A.primitive_zeta12 M U xU m g =
        r q (g q) * allSlotEvaluation F A.zeta12 A.primitive_zeta12 M U xU m (Function.update g q 1) := by
    intro q hq g
    have hn : q.val ∉ T := (Finset.mem_filter.mp hq).2
    have he : q.val ∉ C.exceptional := fun h => hn (hT h)
    have hh := allSlotEvaluation_fixed_reference A P C U q he xU
      (fun k m a => HC_tensor_added_slot_fixed A P C K hK f T hT hbad htail U xU hxU q hn k m a) m g
    simpa only [r] using hh
  have hformula := finite_update_factorization
    (fun g => allSlotEvaluation F A.zeta12 A.primitive_zeta12 M U xU m g) r s hs a
  have hreset : (fun q : U => if q ∈ s then 1 else a q) =
      extendCover F A.zeta12 A.primitive_zeta12 T U (fun q => a ⟨q.val, hTU q.property⟩) := by
    funext q
    by_cases hq : q.val ∈ T
    · simp [s, extendCover, hq]
    · simp [s, extendCover, hq]
  rw [hreset, hxU m (extendCover F A.zeta12 A.primitive_zeta12 T U (fun q => a ⟨q.val, hTU q.property⟩)),
    finiteProductInsertion_extend F A.zeta12 A.primitive_zeta12 T U hTU, ← hxT] at hformula
  exact hformula
end DedekindZetaZeroFree.FourierContinuation.CurrentReferenceTailFormula

end
