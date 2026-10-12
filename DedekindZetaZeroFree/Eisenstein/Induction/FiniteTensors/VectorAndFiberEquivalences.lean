module

public import DedekindZetaZeroFree.Eisenstein.Induction.LocalModels.VectorAndFiberEquivalences

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open NumberField MomentSources KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def sourceLevel (s : RestrictedTensorSimple.Level (FaithfulSource.RepairedInducing.bad R P C)) :
    RestrictedTensorSimple.Level (LiteralSource.bad R.A P C) :=
  ⟨s.val, by
    rw [← show FaithfulSource.RepairedInducing.bad R P C = LiteralSource.bad R.A P C from
      PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.badSet_eq_fullBad
        F R.A.zeta12 R.A.primitive_zeta12 P C]
    exact s.property⟩

theorem coreEquiv_stage
    (s : RestrictedTensorSimple.Level (FaithfulSource.RepairedInducing.bad R P C))
    (x : RestrictedTensorSimple.Stage (FaithfulSource.RepairedInducing.Plus R N P C) s.val) :
    coreEquiv R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s x) =
      RestrictedTensorSimple.stageInclusion (LiteralSource.Plus R.A P C)
        (LiteralSource.plusReference R.A P C) (LiteralSource.bad R.A P C)
        (sourceLevel R P C s) x := by
  exact RestrictedTensorSimple.equalBadEquiv_stage
    (LiteralSource.Plus R.A P C) (LiteralSource.plusReference R.A P C)
    (FaithfulSource.RepairedInducing.bad R P C) (LiteralSource.bad R.A P C)
    (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.badSet_eq_fullBad
      F R.A.zeta12 R.A.primitive_zeta12 P C) s x

theorem comparison_stage_pure
    (s : RestrictedTensorSimple.Level (FaithfulSource.RepairedInducing.bad R P C))
    (y : ∀ j : s.val, FaithfulSource.RepairedInducing.Fiber R P C j.val) :
    FaithfulSource.RepairedInducing.comparisonSmooth R P C
      (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ y)) =
      LiteralSource.comparison R.A P C
        (RestrictedTensorSimple.stageInclusion _ _ _ (sourceLevel R P C s)
          (PiTensorProduct.tprod ℂ y)) := by
  simp only [FaithfulSource.RepairedInducing.comparisonSmooth,
    LiteralSource.comparison, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [FaithfulSource.RepairedInducing.finiteCoreEquiv_stage_pure,
    KPGlobalResidualConstruction.ScalarAbsorption.absorb_stage,
    KPGlobalResidualConstruction.ScalarAbsorption.stageEquiv_pure]
  simp only [map_smul]
  rfl

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
