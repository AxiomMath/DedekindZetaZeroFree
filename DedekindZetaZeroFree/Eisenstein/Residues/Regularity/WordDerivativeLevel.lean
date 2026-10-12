module

public import DedekindZetaZeroFree.Eisenstein.Residues.ResidualRepresentations.WordDerivativeRange

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

theorem actual_word_global_level
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : KPLiteralRaw.G F ζ hζ → ℂ)
    (hf : ∀g u, u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U → f (g*u)=f g)
    (w : List (Fin (groupDimension F))) :
    ∀g u, u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U →
      actualRightWord F ζ hζ w f (g*u) = actualRightWord F ζ hζ w f g := by
  intro g u hu
  rw [EisensteinSmoothGerms.ScalarSource.level_matching F ζ hζ U] at hu
  obtain ⟨v,hv,rfl⟩ := hu
  apply ResidueContinuity.ScalarSourceJointContinuity.actual_word_right_level f _ w g ⟨v,hv⟩
  intro a j
  apply hf a j.val.val
  rw [EisensteinSmoothGerms.ScalarSource.level_matching F ζ hζ U]
  exact Subgroup.mem_map.mpr ⟨j.val,j.property,rfl⟩

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
