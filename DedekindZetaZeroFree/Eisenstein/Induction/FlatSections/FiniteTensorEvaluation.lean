module

public import DedekindZetaZeroFree.Eisenstein.Induction.FiniteTensors.VectorAndFiberEquivalences

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open NumberField MomentSources KPGlobalTorusFiniteStages FaithfulSource.RepairedInducing
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem comparison_stage
    (s : RestrictedTensorSimple.Level (bad R P C))
    (y : RestrictedTensorSimple.Stage (Fiber R P C) s.val) :
    comparisonSmooth R P C (RestrictedTensorSimple.stageInclusion _ _ _ s y) =
      LiteralSource.comparison R.A P C
        (RestrictedTensorSimple.stageInclusion _ _ _ (sourceLevel R P C s) y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    simp only [map_smul, comparison_stage_pure]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency true in
theorem scalar_stage_raw
    (s : RestrictedTensorSimple.Level (bad R P C))
    (x : RestrictedTensorSimple.Stage (Plus R N P C) s.val) (g : Raw R)
    (htail : ∀ p, p ∉ s.val → localValue R N P C p (g p)
      (plusReference R N P C p) = reference R P C p) :
    scalarSourceEvaluator R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s x)
      (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)) =
      LiteralSource.rawCoreInsertion R.A P C
        (coreEquiv R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s x)) g := by
  change (comparisonSmooth R P C (rawCoreVector R N P C g
    (RestrictedTensorSimple.stageInclusion _ _ _ s x))).val.val 1 = _
  rw [rawCoreVector_stage R N P C s g htail, coreEquiv_stage]
  have ht : ∀ p, p ∉ (sourceLevel R P C s).val →
      LiteralSource.localValue R.A P C p (g p) (LiteralSource.plusReference R.A P C p) =
        LiteralSource.reference R.A P C p := by
    intro p hp
    rw [← reference_eq R N P C p, ← localValue_eq R N P C p]
    exact htail p hp
  refine Eq.trans ?_ (LiteralSource.rawCoreInsertion_stage R.A P C
    (sourceLevel R P C s) x g ht).symm
  unfold stageVector LiteralSource.rawStageValue
  simp only [LinearMap.comp_apply, LiteralSource.rationalEvaluation]
  rw [comparison_stage]
  have hm : (fun p : s.val => localValue R N P C p (g p)) =
      (fun p : s.val => LiteralSource.localValueMap R.A P C p.val (g p.val)) := by
    funext p
    rcases p with ⟨p, hp⟩
    cases p <;> rfl
  exact congrArg (fun y : RestrictedTensorSimple.Stage (Fiber R P C) s.val =>
    (LiteralSource.comparison R.A P C
      (RestrictedTensorSimple.stageInclusion _ _ _ (sourceLevel R P C s) y)).val.val 1)
    (congrArg (fun m => PiTensorProduct.map m x) hm)

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
