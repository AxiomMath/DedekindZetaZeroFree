module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.UpperRootTensorAction

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources FourierContinuation.HCGeneration FourierContinuation.LiteralSource
open KPContActualSphericalRightFieldIdentification
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def NativeLieComparison (M : ∀ q, LocalImageData R q)
    (e : ∀ p, actualLocal R M p) (E : Finset (KPHilbert.Place F))
    (L : RestrictedTensorSimple.Core (actualLocal R M) e E →ₗ[ℂ] Functions R) : Prop :=
  ∀ (s : RestrictedTensorSimple.Level E) (w : InfinitePlace F)
    (hw : Sum.inl w ∈ s.val) (b : Fin 6)
    (x : RestrictedTensorSimple.Stage (actualLocal R M) s.val),
    L (RestrictedTensorSimple.stageInclusion _ e E s
      (tensorSlot ⟨Sum.inl w,hw⟩ (localOperation R M (Sum.inl w) [.inr b]) x)) =
    actualRight F R.A.zeta12 R.A.primitive_zeta12
      ((actualLieIndexEquiv (F := F)).symm (w,b))
      (L (RestrictedTensorSimple.stageInclusion _ e E s x))

def SourceNativeLie {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (D : SourceFactorization R Q T) : Prop :=
  NativeLieComparison R D.finiteData D.references D.bad D.coreMap

variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
local notation "H" => actualImageData R P C μ hμ
local notation "W" => actualLocal R H
local notation "E" => bad R.A P C
local notation "e" => actualReference R P C μ hμ

theorem actualCoreResidue_nativeLie (N : TraceHaarTransport R) :
    NativeLieComparison R H e E (actualCoreResidue R P C μ hμ N) := by
  intro s w hw b x
  let i := (actualLieIndexEquiv (F := F)).symm (w,b)
  have hh := actualCoreResidue_stage_generator R P C μ hμ N s (.lie i) x
  have hi : actualLieIndexEquiv (F := F) i = (w,b) := Equiv.apply_symm_apply _ _
  have hop := congrArg
    (fun a : KPSmoothActualFlowData.B F =>
      tensorSlot (V := fun j : s.val => W j.val)
        ⟨Sum.inl a.1,s.property (by simp [bad,KPGlobalResidualConstruction.ScalarAbsorption.fullBad])⟩
        (localOperation R (imageData R P C H) (Sum.inl a.1) [.inr a.2])) hi
  change actualStageGenerator R P C μ hμ s (.lie i) =
    tensorSlot (V := fun j : s.val => W j.val) ⟨Sum.inl w,hw⟩
      (localOperation R (imageData R P C H) (Sum.inl w) [.inr b]) at hop
  rw [hop] at hh
  exact hh
end DedekindZetaZeroFree.RootDerivatives

end
