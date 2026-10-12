module

public import DedekindZetaZeroFree.Eisenstein.Induction.TorusEvaluation
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RationalPeriodization.EvaluatorInjectivity

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages
open PrincipalOfKP.ResidueCoreBridge.CanonicalBinding
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

private theorem absorption_cast (B : Finset (KPHilbert.Place F))
    (hB : B = KPGlobalResidualConstruction.ScalarAbsorption.fullBad
      (A := InfinitePlace F) C.exceptional)
    (s : RestrictedTensorSimple.Level B) (y : ∀ j : s.val, Fiber R P C j)
    (L : RestrictedTensorSimple.Core (Fiber R P C) (reference R P C)
      (KPGlobalResidualConstruction.ScalarAbsorption.fullBad (A := InfinitePlace F) C.exceptional) ≃ₗ[ℂ]
      RestrictedTensorSimple.Core (LocalFiber F R.A.zeta12 R.A.primitive_zeta12 P C)
        (localReference F R.A.zeta12 R.A.primitive_zeta12 P C) C.exceptional)
    (hL : ∀ s y, L (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ y)) =
      (∏ w : s.val.toLeft, y ⟨Sum.inl w.val, Finset.mem_toLeft.mp w.property⟩) •
        RestrictedTensorSimple.stageInclusion _ _ C.exceptional
          ⟨s.val.toRight, by
            intro q hq
            exact Finset.mem_toRight.mpr
              (s.property (by simp [KPGlobalResidualConstruction.ScalarAbsorption.fullBad, hq]))⟩
          (PiTensorProduct.tprod ℂ (fun q : s.val.toRight =>
            y ⟨Sum.inr q.val, Finset.mem_toRight.mp q.property⟩))) :
    (Eq.mpr (congrArg (fun B => RestrictedTensorSimple.Core (Fiber R P C) (reference R P C) B ≃ₗ[ℂ]
      RestrictedTensorSimple.Core (LocalFiber F R.A.zeta12 R.A.primitive_zeta12 P C)
        (localReference F R.A.zeta12 R.A.primitive_zeta12 P C) C.exceptional) hB) L)
      (RestrictedTensorSimple.stageInclusion _ _ B s (PiTensorProduct.tprod ℂ y)) =
      (∏ w : s.val.toLeft, y ⟨Sum.inl w.val, Finset.mem_toLeft.mp w.property⟩) •
        RestrictedTensorSimple.stageInclusion _ _ C.exceptional
          ⟨s.val.toRight, by
            intro q hq
            apply Finset.mem_toRight.mpr
            apply s.property
            rw [hB]
            simp [KPGlobalResidualConstruction.ScalarAbsorption.fullBad, hq]⟩
          (PiTensorProduct.tprod ℂ (fun q : s.val.toRight =>
            y ⟨Sum.inr q.val, Finset.mem_toRight.mp q.property⟩)) := by
  subst B
  exact hL s y

theorem finiteCoreEquiv_stage_pure (s : RestrictedTensorSimple.Level (bad R P C))
    (y : ∀ j : s.val, Fiber R P C j) :
    finiteCoreEquiv R P C (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ y)) =
      (∏ w : s.val.toLeft, y ⟨Sum.inl w.val, Finset.mem_toLeft.mp w.property⟩) •
        RestrictedTensorSimple.stageInclusion _ _ C.exceptional
          ⟨s.val.toRight, by
            intro q hq
            exact Finset.mem_toRight.mpr
              (s.property (finite_mem_badSet F R.A.zeta12 R.A.primitive_zeta12 P C q hq))⟩
          (PiTensorProduct.tprod ℂ (fun q : s.val.toRight =>
            y ⟨Sum.inr q.val, Finset.mem_toRight.mp q.property⟩)) := by
  unfold finiteCoreEquiv
  apply absorption_cast R P C
  · exact badSet_eq_fullBad F R.A.zeta12 R.A.primitive_zeta12 P C
  intro s y
  exact (KPGlobalResidualConstruction.ScalarAbsorption.absorb_stage _ _ C.exceptional s
    (PiTensorProduct.tprod ℂ y)).trans (by
      rw [KPGlobalResidualConstruction.ScalarAbsorption.stageEquiv_pure, map_smul]
      rfl)

def unitaryComparison : FiberCore R P C →ₗ[ℂ]
    KPGlobalTorusPeriodizationInverse.ProductUnitary F R.A.zeta12 R.A.primitive_zeta12 P :=
  (finiteTensorMap R P C).comp (finiteCoreEquiv R P C).toLinearMap

theorem unitaryComparison_full_raw (s : RestrictedTensorSimple.Level (bad R P C))
    (y : ∀ j : s.val, Fiber R P C j) (raw : Raw R)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F R.A.zeta12 R.A.primitive_zeta12 q)
    (e : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F R.A.zeta12
      R.A.primitive_zeta12 (Sum.inr q) (raw (Sum.inr q)))
    (he : KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 raw) = e.val) :
    (unitaryComparison R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (PiTensorProduct.tprod ℂ y))).val.val e =
      (∏ w : s.val.toLeft, y ⟨Sum.inl w.val, Finset.mem_toLeft.mp w.property⟩) *
      (∏ w, (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
        R.A.primitive_zeta12 (raw (Sum.inl w)).epsilon : ℂ)) *
      ∏ᶠ q, localUntwistedEvaluation F R.A.zeta12 R.A.primitive_zeta12 P C q
        (if h : q ∈ s.val.toRight then y ⟨Sum.inr q, Finset.mem_toRight.mp h⟩
         else localReference F R.A.zeta12 R.A.primitive_zeta12 P C q) (t q) := by
  unfold unitaryComparison
  rw [LinearMap.comp_apply]
  change (finiteTensorMap R P C (finiteCoreEquiv R P C
    (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ y)))).val.val e = _
  rw [finiteCoreEquiv_stage_pure, map_smul, finiteTensorMap_stage]
  change _ * (finiteTensorRealization F R.A.zeta12 R.A.primitive_zeta12 P C s.val.toRight _
    (PiTensorProduct.tprod ℂ _)).val.val e = _
  rw [EisensteinReferenceSections.FullTorusFormula.finiteTensorRealization_full_raw_formula F R.A.zeta12
    R.A.primitive_zeta12 P C _ _ _ raw t e ht he]
  ring

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
