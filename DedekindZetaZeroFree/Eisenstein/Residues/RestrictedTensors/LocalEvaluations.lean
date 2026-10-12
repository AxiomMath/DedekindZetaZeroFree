module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LocalActionAlgebrasAndCommutants
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.OperatorWords

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources HCGeneration KPGlobalResidualConstruction
open KPContActualSphericalRightFieldIdentification
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
local notation "H" => actualImageData R P C μ hμ
local notation "W" => actualLocal R H
local notation "E" => bad R.A P C
local notation "e" => actualReference R P C μ hμ
local notation "A" => actualLocalAlgebra R H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem actualCoreResidue_native_slots (N : TraceHaarTransport R) :
∀ t : RestrictedTensorSimple.Level E,
    let L := (actualCoreResidue R P C μ hμ N).comp (RestrictedTensorSimple.stageInclusion _ e E t)
    (∀ (w : NumberField.InfinitePlace F) (hw : Sum.inl w ∈ t.val)
      (k : KPCplxCharacterHaar.ComplexSU2),
      ∃ a : Group R, ∀ x,
        L (tensorSlot ⟨Sum.inl w, hw⟩ (complexGenerator (Sum.inl k)) x) =
          KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a (L x)) ∧
    (∀ (w : NumberField.InfinitePlace F) (hw : Sum.inl w ∈ t.val) (b : Fin 6),
      ∃ j : Fin (KPContActualSphericalRightFieldIdentification.groupDimension F), ∀ x,
        L (tensorSlot ⟨Sum.inl w, hw⟩ (complexGenerator (Sum.inr b)) x) =
          KPContActualSphericalRightFieldIdentification.actualRight
            F R.A.zeta12 R.A.primitive_zeta12 j (L x)) ∧
    (∀ (q : KPFinitePlace F) (hq : Sum.inr q ∈ t.val) (b : LocalOperation R (Sum.inr q)),
      ∃ a : Group R, ∀ x,
        L (tensorSlot ⟨Sum.inr q, hq⟩ (localOperation R H (Sum.inr q) b) x) =
          KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a (L x)) := by
  intro t
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro w hw k
    refine ⟨complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k, ?_⟩
    intro x
    exact actualCoreResidue_stage_generator R P C μ hμ N t (.compact w k) x
  · intro w hw b
    let j := (actualLieIndexEquiv (F := F)).symm (w,b)
    refine ⟨j,?_⟩
    intro x
    have he : actualStageGenerator R P C μ hμ t (.lie j) =
        tensorSlot (V := fun k : t.val => W k.val) ⟨Sum.inl w,hw⟩
          (complexGenerator (.inr b)) := by
      let slot (wb : InfinitePlace F × Fin 6) :
          Module.End ℂ (RestrictedTensorSimple.Stage W t.val) :=
        tensorSlot (V := fun k : t.val => W k.val)
          ⟨Sum.inl wb.1,t.property (by simp [bad,ScalarAbsorption.fullBad])⟩
          (localOperation R H (Sum.inl wb.1) [.inr wb.2])
      change slot (actualLieIndexEquiv (F := F) j) = slot (w,b)
      exact congrArg slot ((actualLieIndexEquiv (F := F)).apply_symm_apply (w,b))
    exact (congrArg (fun T : Module.End ℂ (RestrictedTensorSimple.Stage W t.val) =>
      actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E t (T x))) he).symm.trans
      (actualCoreResidue_stage_generator R P C μ hμ N t (.lie j) x)
  · intro q hq a
    obtain ⟨raw,hr⟩ := QuotientGroup.mk'_surjective
      (KPPGLLocalCover.splitScalarSubgroup F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) a
    refine ⟨KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) raw),?_⟩
    intro x
    have he : actualStageGenerator R P C μ hμ t (.finite q hq raw) =
        tensorSlot (V := fun k : t.val => W k.val) ⟨Sum.inr q,hq⟩
          (localOperation R H (Sum.inr q) a) := by
      change tensorSlot (V := fun k : t.val => W k.val) ⟨Sum.inr q,hq⟩
        (localOperation R H (Sum.inr q) (KPPGLLocalCover.coverQuotient F R.A.zeta12
          R.A.primitive_zeta12 (Sum.inr q) raw)) = _
      exact congrArg (fun g => tensorSlot (V := fun k : t.val => W k.val)
        ⟨Sum.inr q,hq⟩ (localOperation R H (Sum.inr q) g)) hr
    exact (congrArg (fun T : Module.End ℂ (RestrictedTensorSimple.Stage W t.val) =>
      actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E t (T x))) he).symm.trans
      (actualCoreResidue_stage_generator R P C μ hμ N t (.finite q hq raw) x)
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
