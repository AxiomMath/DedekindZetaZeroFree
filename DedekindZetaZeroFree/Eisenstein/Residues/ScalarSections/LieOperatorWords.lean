module

public import DedekindZetaZeroFree.Eisenstein.Residues.ScalarSections.FinitePlaceActions
public import DedekindZetaZeroFree.Eisenstein.Residues.ScalarSections.ReflattenedWordCompatibility
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RestrictedTensorDifferentialWords

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField KPGlobalTorusFiniteStages HCGeneration TensorActionSource
open KPContActualSphericalRightFieldIdentification
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem coreZeroProfile_stage_word
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : List (Fin (groupDimension F)))
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    (coreZeroProfile R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (stageBasisWord R P C s w x))).val =
    actualRightWord F R.A.zeta12 R.A.primitive_zeta12 w
      (coreZeroProfile R P C (RestrictedTensorSimple.stageInclusion _ _ _ s x)).val := by
  simp only [coreZeroProfile_val]
  exact (quotientCoreEvaluator_stage_actualRightWord R P C s w x).symm

theorem coreResidue_stage_word
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : List (Fin (groupDimension F)))
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (stageBasisWord R P C s w x)) =
    actualRightWord F R.A.zeta12 R.A.primitive_zeta12 w
      (coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ s x)) := by
  exact (ownedLiteralResidueFamily (ThetaExpansion.full_product_compact_iwasawa R)).residue_word_of_zero
    w _ _ (coreZeroProfile_stage_word R P C s w x)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
