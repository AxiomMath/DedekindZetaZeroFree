module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.FiniteHarishChandraFamilies
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.FiniteRestrictedStageDecomposition

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace DedekindZetaZeroFree.FourierContinuation.CurrentTailLevel
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralScalarHCExtraction
open KPLiteralScalarHCFiniteDecomposition KPGlobalTorusFiniteStagesIdentification
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
variable (K : Subgroup (KPLiteralRaw.G F A.zeta12 A.primitive_zeta12)) (hK : IwasawaCompact F A.zeta12 A.primitive_zeta12 K)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)
variable (f : Flat F A.zeta12 A.primitive_zeta12 K)

theorem productHCSection_standard_tail :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)), C.exceptional ⊆ T ∧
      ∀ (r : RestrictedCover F ζ hζ)
        (hi : ∀ w : InfinitePlace F, r (Sum.inl w) = 1)
        (hin : ∀ q ∈ T, KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (r (Sum.inr q)) = 1)
        (hout : ∀ q, q ∉ T → KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (r (Sum.inr q)) ∈
          pglCompact F ζ hζ (Sum.inr q))
        (g : KPLiteralRaw.G F ζ hζ),
        (productHCSection F ζ hζ K hK P f).val.val
          (g * scalarQuotient F ζ hζ (amalgamation F ζ hζ r)) =
        (productHCSection F ζ hζ K hK P f).val.val g := by
  obtain ⟨J, hJ⟩ := productHCSection_right_level F ζ hζ K hK P f
  obtain ⟨S, hS⟩ := finite_level_contains_standard_compact_tail F ζ hζ J
  let T := S ∪ C.exceptional
  refine ⟨T, Finset.subset_union_right, ?_⟩
  intro r hi hin hout g
  apply hJ
  apply hS r hi
  · intro q hq
    exact hin q (Finset.mem_union_left _ hq)
  · intro q hq
    by_cases hT : q ∈ T
    · rw [hin q hT]; exact Subgroup.one_mem _
    · exact hout q hT

open KPLiteralScalarHCFiniteProduct KPLiteralScalarHCCompactOrbit KPCplxCharacterHaar
open KPLiteralScalarHCSliceCharts

open NativeScalarMixedTensorGeneration CurrentFiniteFamily

open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Source → Source
open scoped TensorProduct
local instance (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (j : InfinitePlace F ⊕ T) :
    AddCommGroup (mixedSource F ζ hζ (nativeInducingData A P C) T j) := by
  cases j with
  | inl w => dsimp [mixedSource]; infer_instance
  | inr q => exact SourceReconstruction.localPlusAdd F ζ hζ (nativeInducingData A P C) (Sum.inr q.val)
local instance (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (j : InfinitePlace F ⊕ T) :
    Module ℂ (mixedSource F ζ hζ (nativeInducingData A P C) T j) := by
  cases j with
  | inl w => dsimp [mixedSource]; infer_instance
  | inr q => exact SourceReconstruction.localPlusModule F ζ hζ (nativeInducingData A P C) (Sum.inr q.val)

end DedekindZetaZeroFree.FourierContinuation.CurrentTailLevel

end
