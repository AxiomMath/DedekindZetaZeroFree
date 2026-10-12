module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.LieDerivatives

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField KPGlobalTorusFiniteStages HCGeneration
open KPContActualSphericalRightFieldIdentification
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def stageBasisWord (s : RestrictedTensorSimple.Level (bad R.A P C)) :
    List (Fin (groupDimension F)) →
      Module.End ℂ (RestrictedTensorSimple.Stage (Plus R.A P C) s.val)
  | [] => LinearMap.id
  | i :: w => (stageLieSlot R P C s (actualLieIndexEquiv (F := F) i).1
      (s.property (by simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad]))
      (actualLieIndexEquiv (F := F) i).2).comp (stageBasisWord s w)

theorem quotientCoreEvaluator_stage_actualRightWord
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : List (Fin (groupDimension F)))
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    actualRightWord F ζ hζ w
      (quotientCoreEvaluator R.A P C (RestrictedTensorSimple.stageInclusion _ _ _ s x)) =
    quotientCoreEvaluator R.A P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (stageBasisWord R P C s w x)) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [actualRightWord, ih]
    exact quotientCoreEvaluator_stage_actualRight R P C s i _

def evaluatedStageBasisWord (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : List (Fin (groupDimension F))) :
    RestrictedTensorSimple.Stage (Plus R.A P C) s.val →ₗ[ℂ] MomentSources.Functions R :=
  (quotientCoreEvaluator R.A P C).comp
    ((RestrictedTensorSimple.stageInclusion _ _ _ s).comp (stageBasisWord R P C s w))

@[simp] theorem evaluatedStageBasisWord_apply
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : List (Fin (groupDimension F)))
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    evaluatedStageBasisWord R P C s w x = actualRightWord F ζ hζ w
      (quotientCoreEvaluator R.A P C (RestrictedTensorSimple.stageInclusion _ _ _ s x)) :=
  (quotientCoreEvaluator_stage_actualRightWord R P C s w x).symm

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
