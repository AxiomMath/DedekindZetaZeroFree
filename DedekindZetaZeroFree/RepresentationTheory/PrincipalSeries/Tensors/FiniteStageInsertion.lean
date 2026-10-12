module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.FiniteHarishChandraFamilies
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RestrictedTensorProduct

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.CurrentNativeStage
open NativeScalarMixedTensorGeneration
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "M" => CurrentFiniteFamily.nativeInducingData A P C
local notation "r₀" => LiteralSource.plusReference A P C
local notation "Raw" => KPAdelicCoverRestrictedProduct.RestrictedCover F A.zeta12 A.primitive_zeta12
variable (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
local instance (j : InfinitePlace F ⊕ T) : AddCommGroup (mixedSource F A.zeta12 A.primitive_zeta12 M T j) := by
  cases j with
  | inl w => dsimp [mixedSource]; infer_instance
  | inr q => exact SourceReconstruction.localPlusAdd F A.zeta12 A.primitive_zeta12 M (Sum.inr q.val)
local instance (j : InfinitePlace F ⊕ T) : Module ℂ (mixedSource F A.zeta12 A.primitive_zeta12 M T j) := by
  cases j with
  | inl w => dsimp [mixedSource]; infer_instance
  | inr q => exact SourceReconstruction.localPlusModule F A.zeta12 A.primitive_zeta12 M (Sum.inr q.val)

def fullStage (hT : C.exceptional ⊆ T) : RestrictedTensorSimple.Level (LiteralSource.bad A P C) :=
  ⟨Finset.univ.disjSum T, by
    intro v hv
    change v ∈ KPGlobalResidualConstruction.ScalarAbsorption.fullBad (A := InfinitePlace F) C.exceptional at hv
    cases v with
    | inl w => simp
    | inr q =>
      have hq : q ∈ C.exceptional := by
        simpa [KPGlobalResidualConstruction.ScalarAbsorption.fullBad] using hv
      simpa using hT hq⟩

def slotIndex (hT : C.exceptional ⊆ T) : (fullStage A P C T hT).val ≃ InfinitePlace F ⊕ T where
  toFun j := match j with
    | ⟨Sum.inl w, _⟩ => Sum.inl w
    | ⟨Sum.inr q, hq⟩ => Sum.inr ⟨q, by simpa [fullStage] using hq⟩
  invFun j := match j with
    | Sum.inl w => ⟨Sum.inl w, by simp [fullStage]⟩
    | Sum.inr q => ⟨Sum.inr q.val, by simpa [fullStage] using q.property⟩
  left_inv j := by rcases j with ⟨w | q, hj⟩ <;> rfl
  right_inv j := by cases j <;> rfl

 def slotVectorEquiv (hT : C.exceptional ⊆ T) (j : InfinitePlace F ⊕ T) :
    LiteralSource.Plus A P C
      ((slotIndex A P C T hT).symm j).val ≃ₗ[ℂ]
      mixedSource F A.zeta12 A.primitive_zeta12 M T j := by
  cases j with
  | inl w => exact LinearEquiv.refl ℂ _
  | inr q => exact LinearEquiv.refl ℂ _

def nativeStageEquiv (hT : C.exceptional ⊆ T) :
    RestrictedTensorSimple.Stage (LiteralSource.Plus A P C) (fullStage A P C T hT).val ≃ₗ[ℂ]
      PiTensorProduct ℂ (mixedSource (ι := InfinitePlace F) F A.zeta12 A.primitive_zeta12 M T) :=
  (PiTensorProduct.reindex ℂ
    (fun j : (fullStage A P C T hT).val => LiteralSource.Plus A P C j.val)
    (slotIndex A P C T hT)).trans (PiTensorProduct.congr (slotVectorEquiv A P C T hT))

def nativeCoreInsertion (hT : C.exceptional ⊆ T) :
    PiTensorProduct ℂ (mixedSource (ι := InfinitePlace F) F A.zeta12 A.primitive_zeta12 M T) →ₗ[ℂ]
      RestrictedTensorSimple.Core (LiteralSource.Plus A P C) r₀ (LiteralSource.bad A P C) :=
  (RestrictedTensorSimple.stageInclusion (LiteralSource.Plus A P C) r₀ (LiteralSource.bad A P C) (fullStage A P C T hT)).comp
    (nativeStageEquiv A P C T hT).symm.toLinearMap

def stageComponents (hT : C.exceptional ⊆ T)
    (x : ∀ j : InfinitePlace F ⊕ T, mixedSource F A.zeta12 A.primitive_zeta12 M T j)
    (j : (fullStage A P C T hT).val) : LiteralSource.Plus A P C j.val :=
  match j with
  | ⟨Sum.inl w, _⟩ => x (Sum.inl w)
  | ⟨Sum.inr q, hq⟩ => x (Sum.inr ⟨q, by simpa [fullStage] using hq⟩)

theorem nativeStageEquiv_pure (hT : C.exceptional ⊆ T)
    (x : ∀ j : InfinitePlace F ⊕ T, mixedSource F A.zeta12 A.primitive_zeta12 M T j) :
    nativeStageEquiv A P C T hT
      (PiTensorProduct.tprod ℂ (stageComponents A P C T hT x)) =
        PiTensorProduct.tprod ℂ x := by
  simp only [nativeStageEquiv, LinearEquiv.trans_apply, PiTensorProduct.reindex_tprod,
    PiTensorProduct.congr_tprod, Equiv.apply_symm_apply]
  congr 1
  funext j
  cases j <;> rfl

theorem nativeCoreInsertion_pure (hT : C.exceptional ⊆ T)
    (x : ∀ j : InfinitePlace F ⊕ T, mixedSource F A.zeta12 A.primitive_zeta12 M T j) :
    nativeCoreInsertion A P C T hT (PiTensorProduct.tprod ℂ x) =
      RestrictedTensorSimple.stageInclusion (LiteralSource.Plus A P C) r₀ (LiteralSource.bad A P C) (fullStage A P C T hT)
        (PiTensorProduct.tprod ℂ (stageComponents A P C T hT x)) := by
  dsimp only [nativeCoreInsertion, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← nativeStageEquiv_pure A P C T hT x]
  exact congrArg (RestrictedTensorSimple.stageInclusion (LiteralSource.Plus A P C) r₀ (LiteralSource.bad A P C) (fullStage A P C T hT))
    ((nativeStageEquiv A P C T hT).symm_apply_apply _)

end DedekindZetaZeroFree.FourierContinuation.CurrentNativeStage

end
