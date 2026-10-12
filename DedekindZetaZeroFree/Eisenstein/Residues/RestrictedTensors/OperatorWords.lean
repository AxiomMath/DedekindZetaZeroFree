module

public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.Regularity
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ImageQuotients.OperatorWordSpan

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources HCGeneration
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

theorem actual_stageImageQuotient (s : RestrictedTensorSimple.Level E) :
    stageImageQuotient R P C H s = TensorActionSource.sourceStageQuotient R H s.val := rfl

def actualStageGenerator (s : RestrictedTensorSimple.Level E) :
    StageGenerator R P C s → Module.End ℂ (RestrictedTensorSimple.Stage W s.val) :=
  stageImageGenerator R P C H s

theorem actualCoreResidue_stage_generator (N : TraceHaarTransport R)
    (s : RestrictedTensorSimple.Level E) (b : StageGenerator R P C s)
    (x : RestrictedTensorSimple.Stage W s.val) :
    actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E s
      (actualStageGenerator R P C μ hμ s b x)) =
    stageScalarGenerator R P C s b
      (actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E s x)) := by
  obtain ⟨u, rfl⟩ := TensorActionSource.sourceStageQuotient_surjective R H s.val x
  have hq := stageImageQuotient_generator R P C H s b u
  rw [actual_stageImageQuotient] at hq
  change actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E s
    (stageImageGenerator R P C H s b (TensorActionSource.sourceStageQuotient R H s.val u))) = _
  apply Eq.trans (congrArg (fun y : RestrictedTensorSimple.Stage W s.val =>
    actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E s y)) hq.symm)
  apply Eq.trans (actualCoreResidue_source_stage R P C μ hμ N s
    (stageGenerator R P C s b u))
  apply Eq.trans (coreResidue_stage_generator R P C s b u)
  exact congrArg (stageScalarGenerator R P C s b)
    (actualCoreResidue_source_stage R P C μ hμ N s u).symm

def actualStageWord (s : RestrictedTensorSimple.Level E) :
    List (StageGenerator R P C s) → Module.End ℂ (RestrictedTensorSimple.Stage W s.val)
  | [] => LinearMap.id
  | b :: w => (actualStageGenerator R P C μ hμ s b).comp (actualStageWord s w)

theorem actualCoreResidue_stage_word (N : TraceHaarTransport R)
    (s : RestrictedTensorSimple.Level E) (w : List (StageGenerator R P C s))
    (x : RestrictedTensorSimple.Stage W s.val) :
    actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E s
      (actualStageWord R P C μ hμ s w x)) =
    stageScalarWord R P C s w
      (actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E s x)) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E s
      (actualStageGenerator R P C μ hμ s b (actualStageWord R P C μ hμ s w x))) = _
    rw [actualCoreResidue_stage_generator, ih]
    rfl

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
