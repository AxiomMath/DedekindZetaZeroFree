module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RestrictedTensors.FiniteStageExtraction

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.CurrentNativeStage
open LiteralSource NativeScalarMixedTensorGeneration KPAdelicCoverRestrictedProduct KPLiteralChamber
open KPLiteralScalarHCCompactOrbit KPLiteralScalarHCFiniteDecomposition
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "M" => CurrentFiniteFamily.nativeInducingData A P C
variable (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
local instance (j : InfinitePlace F ⊕ T) : AddCommGroup (mixedSource F A.zeta12 A.primitive_zeta12 M T j) := by
  cases j <;> dsimp [mixedSource] <;> infer_instance
local instance (j : InfinitePlace F ⊕ T) : Module ℂ (mixedSource F A.zeta12 A.primitive_zeta12 M T j) := by
  cases j <;> dsimp [mixedSource] <;> infer_instance

theorem nativeCoreInsertion_originalProductScalar (hT : C.exceptional ⊆ T)
    (x : PiTensorProduct ℂ (mixedSource (ι := InfinitePlace F) F A.zeta12 A.primitive_zeta12 M T))
    (r : Raw A) (hi : ∀ w : InfinitePlace F, r (Sum.inl w) = 1)
    (hc : ∀ q, q ∉ T → KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12
      (Sum.inr q) (r (Sum.inr q)) ∈ (C.canonical q).iwasawa.compact.toOpenSubgroup)
    (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    originalProductScalar A P (quotientCoreEvaluator A P C (nativeCoreInsertion A P C T hT x))
      (quotientCoreEvaluator_induced A P C (nativeCoreInsertion A P C T hT x))
      (scalarQuotient F A.zeta12 A.primitive_zeta12 (amalgamation F A.zeta12 A.primitive_zeta12 r) *
        archMatrixInsertion F A.zeta12 A.primitive_zeta12 m) =
      allSlotEvaluation F A.zeta12 A.primitive_zeta12 M T x m
        (stageLocalQuotients F A.zeta12 A.primitive_zeta12 T (fun q => r (Sum.inr q.val))) := by
  change originalProductScalar A P _ _
    (scalarQuotient F A.zeta12 A.primitive_zeta12 (amalgamation F A.zeta12 A.primitive_zeta12 r) *
      scalarQuotient F A.zeta12 A.primitive_zeta12 (amalgamation F A.zeta12 A.primitive_zeta12
        (sectionTuple F A.zeta12 A.primitive_zeta12 m))) = _
  rw [← map_mul,← map_mul,originalProductScalar_core]
  exact nativeCoreInsertion_product_scalar A P C T hT x r hi hc m
end DedekindZetaZeroFree.FourierContinuation.CurrentNativeStage

end
