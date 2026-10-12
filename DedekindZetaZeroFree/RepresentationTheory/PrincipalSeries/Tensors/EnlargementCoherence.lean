module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.TransitionEvaluation

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
namespace DedekindZetaZeroFree.FourierContinuation.CurrentCoherentEnlargement
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralScalarHCExtraction
open FourierContinuation.CurrentNativeStage NativeScalarMixedTensorGeneration
open KPLiteralScalarHCFiniteDecomposition
open KPLiteralScalarHCFiniteOutside KPLiteralScalarHCFiniteProduct KPLiteralScalarHCCompactOrbit
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "M" => FourierContinuation.CurrentFiniteFamily.nativeInducingData A P C
local notation "V" => FourierContinuation.LiteralSource.Plus A P C
local notation "Raw" => RestrictedCover F A.zeta12 A.primitive_zeta12
local notation "bad" => FourierContinuation.LiteralSource.bad A P C
local instance (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (j : InfinitePlace F ⊕ T) : AddCommGroup (mixedSource F A.zeta12 A.primitive_zeta12 M T j) := by
  cases j with
  | inl i => dsimp [mixedSource]; infer_instance
  | inr q => exact FourierContinuation.SourceReconstruction.localPlusAdd F A.zeta12 A.primitive_zeta12 M (Sum.inr q.val)
local instance (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (j : InfinitePlace F ⊕ T) : Module ℂ (mixedSource F A.zeta12 A.primitive_zeta12 M T j) := by
  cases j with
  | inl i => dsimp [mixedSource]; infer_instance
  | inr q => exact FourierContinuation.SourceReconstruction.localPlusModule F A.zeta12 A.primitive_zeta12 M (Sum.inr q.val)

theorem native_HC_tensors_coherent
    (K : Subgroup (KPLiteralRaw.G F A.zeta12 A.primitive_zeta12))
    (hK : IwasawaCompact F A.zeta12 A.primitive_zeta12 K)
    (f : Flat F A.zeta12 A.primitive_zeta12 K)
    (T U : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (hT : C.exceptional ⊆ T) (hU : C.exceptional ⊆ U) (hTU : T ⊆ U)
    (hbad : ∀ q, Bad F q → q ∈ T)
    (htail : ∀ (r : Raw)
      (hi : ∀ w : InfinitePlace F, r (Sum.inl w) = 1)
      (hin : ∀ q ∈ T, KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) (r (Sum.inr q)) = 1)
      (hout : ∀ q, q ∉ T → KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) (r (Sum.inr q)) ∈
        pglCompact F A.zeta12 A.primitive_zeta12 (Sum.inr q))
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
        ((finiteProductInsertion F A.zeta12 A.primitive_zeta12 U a).val * archMatrixInsertion F A.zeta12 A.primitive_zeta12 m)) :
    RestrictedTensorSimple.transition V (FourierContinuation.LiteralSource.plusReference A P C) bad
      (fullStage A P C T hT) (fullStage A P C U hU)
      (by intro j hj; cases j with
        | inl w => simp [fullStage]
        | inr q => simpa [fullStage] using hTU (by simpa [fullStage] using hj))
      ((nativeStageEquiv A P C T hT).symm xT) =
      (nativeStageEquiv A P C U hU).symm xU := by
  have he :
      FourierContinuation.CurrentTransitionEvaluation.nativeTransition A P C T U hT hU hTU xT = xU := by
    apply FourierContinuation.CurrentReferenceFactorization.allSlotEvaluation_injective A P C U
    funext m a
    rw [FourierContinuation.CurrentTransitionEvaluation.nativeTransition_evaluation]
    exact (FourierContinuation.CurrentReferenceTailFormula.HC_tensor_reference_tail_formula
      A P C K hK f T U hT hTU hbad htail xT xU hxT hxU m a).symm
  have h := congrArg (nativeStageEquiv A P C U hU).symm he
  dsimp only [FourierContinuation.CurrentTransitionEvaluation.nativeTransition,
    LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h
end DedekindZetaZeroFree.FourierContinuation.CurrentCoherentEnlargement

end
