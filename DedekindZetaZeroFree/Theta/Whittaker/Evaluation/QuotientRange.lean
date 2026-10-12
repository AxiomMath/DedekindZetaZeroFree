module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.EnlargementCoherence
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.ProductScalarRecovery

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
namespace DedekindZetaZeroFree.FourierContinuation.CurrentGlobalSource
open LiteralSource CurrentNativeStage CurrentFiniteFamily NativeScalarMixedTensorGeneration
open KPAdelicCoverRestrictedProduct KPLiteralRaw KPLiteralScalarHCExtraction
open KPLiteralScalarHCCompactOrbit KPLiteralScalarHCFiniteProduct
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local instance (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (j : InfinitePlace F ⊕ T) :
    AddCommGroup (mixedSource F A.zeta12 A.primitive_zeta12 (nativeInducingData A P C) T j) := by
  cases j <;> dsimp [mixedSource] <;> infer_instance
local instance (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (j : InfinitePlace F ⊕ T) :
    Module ℂ (mixedSource F A.zeta12 A.primitive_zeta12 (nativeInducingData A P C) T j) := by
  cases j <;> dsimp [mixedSource] <;> infer_instance

theorem quotientCoreEvaluator_source_range
    (K : Subgroup (KPLiteralRaw.G F A.zeta12 A.primitive_zeta12))
    (hK : IwasawaCompact F A.zeta12 A.primitive_zeta12 K)
    (f : Flat F A.zeta12 A.primitive_zeta12 K) :
    ∃ x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C),
      quotientCoreEvaluator A P C x = f.val 0 := by
  obtain ⟨S, heS, hS⟩ := CurrentTailLevel.productHCSection_standard_tail
    A K hK P C f
  let T := S ∪ (bad_finite F).toFinset
  have he : C.exceptional ⊆ T := heS.trans Finset.subset_union_left
  have hb : ∀ q, Bad F q → q ∈ T := fun q hq =>
    Finset.mem_union_right S ((bad_finite F).mem_toFinset.mpr hq)
  have ht (U : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hTU : T ⊆ U)
      (r : RestrictedCover F A.zeta12 A.primitive_zeta12)
      (hi : ∀ w : InfinitePlace F, r (Sum.inl w) = 1)
      (hin : ∀ q ∈ U, KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) (r (Sum.inr q)) = 1)
      (hout : ∀ q, q ∉ U → KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) (r (Sum.inr q)) ∈ pglCompact F A.zeta12 A.primitive_zeta12 (Sum.inr q))
      (g : KPLiteralRaw.G F A.zeta12 A.primitive_zeta12) :
      (productHCSection F A.zeta12 A.primitive_zeta12 K hK P f).val.val
        (g * scalarQuotient F A.zeta12 A.primitive_zeta12 (amalgamation F A.zeta12 A.primitive_zeta12 r)) =
      (productHCSection F A.zeta12 A.primitive_zeta12 K hK P f).val.val g := by
    apply hS r hi
    · intro q hq
      exact hin q (hTU (Finset.mem_union_left _ hq))
    · intro q hq
      by_cases hqU : q ∈ U
      · rw [hin q hqU]; exact Subgroup.one_mem _
      · exact hout q hqU
  obtain ⟨xT, hxT⟩ := extractTensor A P C K hK f T
  refine ⟨nativeCoreInsertion A P C T he xT, ?_⟩
  apply originalProductScalar_injective A P _ _
    (quotientCoreEvaluator_induced A P C _) (f.property.1 0)
  rw [originalProductScalar_HC A P K hK f]
  funext g
  obtain ⟨r,m,hi,hg⟩ := groupDecomposition A g
  obtain ⟨U,hTU,hrU⟩ := rawStage A T r
  have heU : C.exceptional ⊆ U := he.trans hTU
  obtain ⟨xU,hxU⟩ := extractTensor A P C K hK f U
  have hc := CurrentCoherentEnlargement.native_HC_tensors_coherent
    A P C K hK f T U he heU hTU hb (ht T (Finset.Subset.refl T)) xT xU hxT hxU
  have hcore : nativeCoreInsertion A P C T he xT = nativeCoreInsertion A P C U heU xU := by
    change RestrictedTensorSimple.stageInclusion _ _ _ _ _ = RestrictedTensorSimple.stageInclusion _ _ _ _ _
    have hi := congrArg (RestrictedTensorSimple.stageInclusion
      (Plus A P C) (plusReference A P C) (bad A P C) (fullStage A P C U heU)) hc
    exact (Module.DirectLimit.of_f ..).symm.trans hi
  rw [hcore,hg]
  rw [nativeCoreInsertion_originalProductScalar A P C U heU xU r hi]
  · rw [hxU]
    apply Eq.symm
    apply remove_tail_at_stage A P K hK f U _ r hi hrU m
    intro o hoa hin hout g
    exact congrArg (fun v => v.val.val 1) (ht U hTU o hoa hin hout g)
  · intro q hq
    exact standard_compact_mem_canonical A P C q (fun h => hq (heU h))
      (fun h => hq (hTU (hb q h))) _ (hrU q hq)
end DedekindZetaZeroFree.FourierContinuation.CurrentGlobalSource

end
