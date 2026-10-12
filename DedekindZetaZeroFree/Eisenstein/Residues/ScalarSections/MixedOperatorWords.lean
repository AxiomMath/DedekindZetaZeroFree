module

public import DedekindZetaZeroFree.Eisenstein.Residues.ScalarSections.LieOperatorWords
public import DedekindZetaZeroFree.Eisenstein.Residues.TensorProducts.CoreCompactCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField KPGlobalTorusFiniteStages HCGeneration TensorActionSource MomentSources
open KPContActualSphericalRightFieldIdentification
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 6400000

inductive StageGenerator (s : RestrictedTensorSimple.Level (bad R.A P C)) where
  | compact (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2)
  | lie (i : Fin (groupDimension F))
  | finite (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
      (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))

def stageFiniteSlot (s : RestrictedTensorSimple.Level (bad R.A P C))
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    Module.End ℂ (RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :=
  tensorSlot ⟨Sum.inr q, hq⟩ (localFiniteAction R P C q a)

theorem coreResidue_stage_finite
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (stageFiniteSlot R P C s q hq a x)) =
    KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12
          (Sum.inr q) a))
      (coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ s x)) := by
  funext g
  change coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
    (stageFiniteSlot R P C s q hq a x)) g =
    coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ s x)
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12
          (Sum.inr q) a))
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, Pi.smul_apply]
    apply congrArg (c • ·)
    change coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (tensorSlot ⟨Sum.inr q, hq⟩ (localFiniteAction R P C q a) (PiTensorProduct.tprod ℂ x))) g = _
    rw [tensorSlot_tprod]
    exact coreResidue_update_finite R P C q a s hq x g
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]

def stageGenerator (s : RestrictedTensorSimple.Level (bad R.A P C)) :
    StageGenerator R P C s → Module.End ℂ (RestrictedTensorSimple.Stage (Plus R.A P C) s.val)
  | .compact w k => compactSlot R.A P C s.val w
      (s.property (by simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad])) k
  | .lie i => stageBasisWord R P C s [i]
  | .finite q hq a => stageFiniteSlot R P C s q hq a

def stageScalarGenerator (s : RestrictedTensorSimple.Level (bad R.A P C)) :
    StageGenerator R P C s → (Functions R → Functions R)
  | .compact w k => KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12
      (KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k)
  | .lie i => actualRight F R.A.zeta12 R.A.primitive_zeta12 i
  | .finite q _ a => KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12
          (Sum.inr q) a))

theorem coreResidue_stage_generator
    (s : RestrictedTensorSimple.Level (bad R.A P C)) (b : StageGenerator R P C s)
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (stageGenerator R P C s b x)) =
    stageScalarGenerator R P C s b
      (coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ s x)) := by
  cases b with
  | compact w k =>
    funext g
    exact coreResidue_stage_compact R P C w k s _ x g
  | lie i => exact coreResidue_stage_word R P C s [i] x
  | finite q hq a => exact coreResidue_stage_finite R P C s q hq a x

def stageWord (s : RestrictedTensorSimple.Level (bad R.A P C)) :
    List (StageGenerator R P C s) → Module.End ℂ (RestrictedTensorSimple.Stage (Plus R.A P C) s.val)
  | [] => LinearMap.id
  | b :: w => (stageGenerator R P C s b).comp (stageWord s w)

def stageScalarWord (s : RestrictedTensorSimple.Level (bad R.A P C)) :
    List (StageGenerator R P C s) → (Functions R → Functions R)
  | [], f => f
  | b :: w, f => stageScalarGenerator R P C s b (stageScalarWord s w f)

theorem coreResidue_stage_mixed_word
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : List (StageGenerator R P C s))
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (stageWord R P C s w x)) =
    stageScalarWord R P C s w
      (coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ s x)) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (stageGenerator R P C s b (stageWord R P C s w x))) = _
    rw [coreResidue_stage_generator, ih]
    rfl

def evaluatedResidueStageWord (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : List (StageGenerator R P C s)) :
    RestrictedTensorSimple.Stage (Plus R.A P C) s.val →ₗ[ℂ] Functions R :=
  (coreResidue R P C).comp ((RestrictedTensorSimple.stageInclusion _ _ _ s).comp
    (stageWord R P C s w))

@[simp] theorem evaluatedResidueStageWord_apply
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : List (StageGenerator R P C s))
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    evaluatedResidueStageWord R P C s w x = stageScalarWord R P C s w
      (coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ s x)) :=
  coreResidue_stage_mixed_word R P C s w x

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
