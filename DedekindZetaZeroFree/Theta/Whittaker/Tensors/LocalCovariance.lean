module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LocalActionAlgebrasAndCommutants
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.OperatorWords

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources HCGeneration KPGlobalResidualConstruction
open KPContActualSphericalRightFieldIdentification
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
local notation "H" => actualImageData R P C μ hμ
local notation "W" => actualLocal R H
local notation "E" => bad R.A P C
local notation "e" => actualReference R P C μ hμ
local notation "A" => actualLocalAlgebra R H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

theorem actual_finite_covariance (N : TraceHaarTransport R) : ∀ q (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (s : RestrictedTensorSimple.Level (bad R.A P C)) (hq : Sum.inr q ∈ s.val)
    (x : ∀ p : s.val, actualLocal R (actualImageData R P C μ hμ) p) g,
    (actualCoreResidue R P C μ hμ N) (RestrictedTensorSimple.stageInclusion _ (actualReference R P C μ hμ) (bad R.A P C) s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q, hq⟩
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
          q ((actualImageData R P C μ hμ) q).inducing ((actualImageData R P C μ hμ) q).inducing.polarization
          ((actualImageData R P C μ hμ) q).haar ((actualImageData R P C μ hμ) q).haar_integer
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
          (x ⟨Sum.inr q, hq⟩))))) g =
    (actualCoreResidue R P C μ hμ N) (RestrictedTensorSimple.stageInclusion _ (actualReference R P C μ hμ) (bad R.A P C) s (PiTensorProduct.tprod ℂ x))
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)) := by
  intro q a s hq v g
  exact actualCoreResidue_update_finite R P C μ hμ N s q hq a v g
theorem actual_complex_covariance (N : TraceHaarTransport R) : ∀ (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2)
    (s : RestrictedTensorSimple.Level (bad R.A P C)) (hw : Sum.inl w ∈ s.val)
    (x : ∀ p : s.val, actualLocal R (actualImageData R P C μ hμ) p) g,
    (actualCoreResidue R P C μ hμ N) (RestrictedTensorSimple.stageInclusion _ (actualReference R P C μ hμ) (bad R.A P C) s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w, hw⟩
        (KPGlobalResidualConstruction.complexCoreSU2Action k (x ⟨Sum.inl w, hw⟩))))) g =
    (actualCoreResidue R P C μ hμ N) (RestrictedTensorSimple.stageInclusion _ (actualReference R P C μ hμ) (bad R.A P C) s (PiTensorProduct.tprod ℂ x))
      (g * KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k) := by
  intro w k t hw v g
  have hh := congrFun (actualCoreResidue_stage_generator R P C μ hμ N t
    (.compact w k) (PiTensorProduct.tprod ℂ v)) g
  change actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion _ _ _ t
    (HCGeneration.tensorSlot ⟨Sum.inl w,hw⟩
      (KPGlobalResidualConstruction.complexCoreCompactLinearMap k) (PiTensorProduct.tprod ℂ v))) g = _ at hh
  rw [HCGeneration.tensorSlot_tprod] at hh
  exact hh
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
