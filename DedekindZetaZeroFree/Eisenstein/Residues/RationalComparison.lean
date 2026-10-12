module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalTensorEvaluation
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Residues.RationalVectorCofactor

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct BigOperators
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField KPGlobalTorusFiniteStages
open KPGlobalResidualConstruction
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem comparison_pure_rational
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : s.val, Fiber R.A P C j.val)
    (t : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12) :
    (comparison R.A P C (RestrictedTensorSimple.stageInclusion
      (Fiber R.A P C) (reference R.A P C) (bad R.A P C) s
      (PiTensorProduct.tprod ℂ x))).val.val t =
    (∏ a : s.val.toLeft, x ⟨.inl a.val, Finset.mem_toLeft.mp a.property⟩) *
      ActualCofactor.rationalStageEval F R.A.zeta12 R.A.primitive_zeta12 P C
        (ScalarAbsorption.rightLevel C.exceptional s).val
        (ScalarAbsorption.rightLevel C.exceptional s).property t
        (fun q => x ⟨.inr q.val, Finset.mem_toRight.mp q.property⟩) := by
  unfold comparison
  simp only [LinearMap.comp_apply]
  rw [ScalarAbsorption.absorb_stage, ScalarAbsorption.stageEquiv_pure]
  simp only [map_smul]
  rw [finiteTensorMap_stage]
  rfl

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
