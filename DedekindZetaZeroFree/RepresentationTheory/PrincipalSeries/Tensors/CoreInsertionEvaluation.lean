module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.FiniteStageInsertion
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.TensorFiberContraction
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.FiniteRestrictedStageDecomposition
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.FiniteLevelsAndNormalizedSectionComparison

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.CurrentNativeStage
open LiteralSource NativeScalarMixedTensorGeneration KPLiteralChamber
open KPLiteralScalarHCFiniteDecomposition KPLiteralScalarHCCompactOrbit
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "M" => CurrentFiniteFamily.nativeInducingData A P C
variable (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming normalized_reference → normalized_reference

theorem reference_tail_localValue (hT : C.exceptional ⊆ T)
    (r : Raw A) (hc : ∀ q, q ∉ T → KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12
      (Sum.inr q) (r (Sum.inr q)) ∈ (C.canonical q).iwasawa.compact.toOpenSubgroup)
    (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    ∀ v, v ∉ (fullStage A P C T hT).val →
      localValue A P C v ((r * sectionTuple F A.zeta12 A.primitive_zeta12 m) v)
        (plusReference A P C v) = reference A P C v := by
  intro v hv
  cases v with
  | inl w => exact False.elim (hv (by simp [fullStage]))
  | inr q =>
    have hq : q ∉ T := by simpa [fullStage] using hv
    have he : q ∉ C.exceptional := fun h => hq (hT h)
    have hfix := plusReference_fixed A P C q he
      ⟨KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12
        (Sum.inr q) (r (Sum.inr q)), hc q hq⟩
    have hval := congrArg (fun f : Plus A P C (Sum.inr q) => f.val 1) hfix
    change (plusReference A P C (Sum.inr q)).val
      (1 * KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12
        (Sum.inr q) (r (Sum.inr q))) = _ at hval
    rw [one_mul] at hval
    change (plusReference A P C (Sum.inr q)).val
      (KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12
        (Sum.inr q) (r (Sum.inr q) * 1)) = _
    rw [mul_one,hval]
    simpa only [plusReference, dif_pos he, reference,
      KPGlobalResidualConstruction.ScalarAbsorption.fullReference] using
      (normalized_reference A P C q he).choose_spec.2
private theorem complexMatrix_section (w : InfinitePlace F)
    (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    complexMatrix A w ((sectionTuple F A.zeta12 A.primitive_zeta12 m) (Sum.inl w)) = m w := by
  apply Units.ext
  ext i j
  simp [sectionTuple, complexMatrix, KPLocalCover.sectionMap, Matrix.GeneralLinearGroup.map]

 def archIndex (hT : C.exceptional ⊆ T) : (fullStage A P C T hT).val.toLeft ≃ InfinitePlace F where
  toFun w := w.val
  invFun w := ⟨w, by simp [fullStage]⟩
  left_inv _ := rfl
  right_inv _ := rfl

 def finiteIndex (hT : C.exceptional ⊆ T) : (fullStage A P C T hT).val.toRight ≃ T where
  toFun q := ⟨q.val, by simpa [fullStage] using q.property⟩
  invFun q := ⟨q.val, by simpa [fullStage] using q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

local instance (j : InfinitePlace F ⊕ T) : AddCommGroup (mixedSource F A.zeta12 A.primitive_zeta12 M T j) := by
  cases j <;> dsimp [mixedSource] <;> infer_instance
local instance (j : InfinitePlace F ⊕ T) : Module ℂ (mixedSource F A.zeta12 A.primitive_zeta12 M T j) := by
  cases j <;> dsimp [mixedSource] <;> infer_instance

theorem nativeCoreInsertion_product_scalar
    (hT : C.exceptional ⊆ T)
    (x : PiTensorProduct ℂ (mixedSource (ι := InfinitePlace F) F A.zeta12 A.primitive_zeta12 M T))
    (r : Raw A) (hi : ∀ w : InfinitePlace F, r (Sum.inl w) = 1)
    (hc : ∀ q, q ∉ T → KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12
      (Sum.inr q) (r (Sum.inr q)) ∈ (C.canonical q).iwasawa.compact.toOpenSubgroup)
    (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    (rawCoreFiber A P C (r * sectionTuple F A.zeta12 A.primitive_zeta12 m)
      (nativeCoreInsertion A P C T hT x)).val.val 1 =
      allSlotEvaluation F A.zeta12 A.primitive_zeta12 M T x m
        (stageLocalQuotients F A.zeta12 A.primitive_zeta12 T (fun q => r (Sum.inr q.val))) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
    congr 1
    rw [nativeCoreInsertion_pure, rawCoreFiber_stage A P C _ _ _
      (reference_tail_localValue A P C T hT r hc m), rawStageFiber_pure]
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
    rw [KPLiteralScalarHCSourceComparison.finiteTensorRealization_one, allSlotEvaluation_pure]
    apply congrArg₂ (· * ·)
    · apply Fintype.prod_equiv (archIndex A P C T hT)
      intro w
      dsimp only [localValue, stageComponents, archIndex]
      rw [show (r * sectionTuple F A.zeta12 A.primitive_zeta12 m) (Sum.inl w.val) =
          (sectionTuple F A.zeta12 A.primitive_zeta12 m) (Sum.inl w.val) by
            change r (Sum.inl w.val) * _ = _; rw [hi w.val, one_mul]]
      rw [complexMatrix_section]
      simp [sectionTuple, KPLocalCover.sectionMap]
    · apply Fintype.prod_equiv (finiteIndex A P C T hT)
      intro q
      dsimp only [localValue, stageComponents, finiteIndex, stageLocalQuotients]
      simp only [RestrictedProduct.mul_apply]
      change ((x (Sum.inr ⟨q.val, _⟩)).val
        (KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q.val)
          (r (Sum.inr q.val) * 1))).val 1 = _
      rw [mul_one]
      rfl
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply]
    exact congrArg₂ (· + ·) hx hy
end DedekindZetaZeroFree.FourierContinuation.CurrentNativeStage

end
