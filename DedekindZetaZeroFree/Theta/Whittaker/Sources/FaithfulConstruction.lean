module

public import DedekindZetaZeroFree.Theta.Periods.RepeatedCorePeriod
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.Injectivity

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources ThetaExpansion TensorActionSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)

variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)

include μ hμ in
theorem exists_faithful_from_initial_plus
    (hR : RootAligned R) (N : TraceHaarTransport R) (hC : C.exceptional = R.A.Sf)
    (u : ∀ j : bad R.A P C, Plus R.A P C j.val)
    (hspherical : ∀ z (p : KPFinitePlace F), p ∉ R.A.Sf →
      ∀ k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p),
        k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) →
      ∀ g, (coreFlatInsertion R P C (RestrictedTensorSimple.stageInclusion _ _ _ ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ u))).val z
        (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) k)) =
        (coreFlatInsertion R P C (RestrictedTensorSimple.stageInclusion _ _ _ ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ u))).val z g)
    (hx : fourier R (KPWildKernelUpperBound.quotientHaar F)
      (coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _
        ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ u))) 1 ≠ 0) :
    Nonempty (NonDegenerate.Faithful R N) := by
  let t : RestrictedTensorSimple.Level (bad R.A P C) := ⟨bad R.A P C,le_rfl⟩
  let x := RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C)
    (bad R.A P C) t (PiTensorProduct.tprod ℂ u)
  obtain ⟨D,hD,hflat⟩ := exists_repeated_core_period_source R P C  hR N x hspherical hx
  let y : ∀ j : t.val, MomentSources.actualLocal R (actualImageData R P C μ hμ) j.val :=
    fun j => TensorActionSource.sourceQuotient R (actualImageData R P C μ hμ) j.val (u j)
  have hy : TensorActionSource.sourceStageQuotient R (actualImageData R P C μ hμ)
      t.val (PiTensorProduct.tprod ℂ u) = PiTensorProduct.tprod ℂ y :=
    PiTensorProduct.map_tprod _ u
  refine ⟨{
    toDictionary := {
      toPeriodSource := D
      finiteData := actualImageData R P C μ hμ
      references := actualReference R P C μ hμ
      bad := bad R.A P C
      bad_exact := ?_
      scalarSlot := TensorSeedSource.scalarSlot R
      coreMap := actualCoreResidue R P C μ hμ N
      selected := fun _ => RestrictedTensorSimple.stageInclusion _ _ _ t (PiTensorProduct.tprod ℂ y)
      selected_eq := ?_
      selected_frozen_stage := fun _ => ⟨t,y,rfl,rfl⟩ }
    core_injective := actualCoreResidue_injective R P C μ hμ N hC
    regular := actualCoreResidue_regular R P C μ hμ N }⟩
  · intro p
    cases p <;> simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad,hC]
  · intro v
    rw [← hy,actualCoreResidue_source_stage]
    exact (hD v).symm
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
