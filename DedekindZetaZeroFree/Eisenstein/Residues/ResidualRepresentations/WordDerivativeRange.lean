module

public import DedekindZetaZeroFree.Eisenstein.Residues.ScalarSections.LieOperatorWords

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages ThetaExpansion TensorActionSource
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C)
  (plusReference R.A P C) (bad R.A P C)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators

theorem coreResidue_word_range (x : V) (w : List (Fin (groupDimension F))) :
    ∃ y : V, coreResidue R P C y = actualRightWord F ζ hζ w (coreResidue R P C x) := by
  obtain ⟨s,u,rfl⟩ := Module.DirectLimit.exists_of x
  exact ⟨RestrictedTensorSimple.stageInclusion _ _ _ s (stageBasisWord R P C s w u),
    coreResidue_stage_word R P C s w u⟩

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
