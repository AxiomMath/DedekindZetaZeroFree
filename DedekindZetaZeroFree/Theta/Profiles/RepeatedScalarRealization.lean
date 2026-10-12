module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.SphericalExteriorInsertion
public import DedekindZetaZeroFree.Theta.Periods.RestrictedTensorIntegration
public import DedekindZetaZeroFree.Theta.Periods.RepeatedCorePeriod

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.RootDerivatives
open FourierContinuation
open FourierContinuation.LiteralSource MomentSources FourierContinuation.HCGeneration TensorActionSource KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
local notation "H" => actualImageData R P C μ hμ
local notation "W" => actualLocal R H
local notation "E" => bad R.A P C
local notation "e" => actualReference R P C μ hμ
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem actual_initial_repeated_realization
    (N : TraceHaarTransport R)
    (hR : RootAligned R) (hC : C.exceptional=R.A.Sf)
    (x : ∀j:E,W j.val) :
    ∃Q:AdmissibleFlatSources R, ∃T:Realization R Q, ∀v,
      T.theta v=actualCoreResidue R P C μ hμ N
        (RestrictedTensorSimple.stageInclusion W e E ⟨E,le_rfl⟩ (PiTensorProduct.tprod ℂ x)) := by
  choose u hu using fun j:E =>
    sourceQuotient_surjective R H j.val (x j)
  have he : sourceStageQuotient R H E (PiTensorProduct.tprod ℂ u)=PiTensorProduct.tprod ℂ x := by
    rw [sourceStageQuotient,PiTensorProduct.map_tprod]
    exact congrArg (PiTensorProduct.tprod ℂ) (funext hu)
  let y := RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C)
    E ⟨E,le_rfl⟩ (PiTensorProduct.tprod ℂ u)
  let Q := repeatedCoreSources R P C y
    (coreFlatInsertion_initial_exterior_spherical R P C hC (PiTensorProduct.tprod ℂ u))
  let B : JointRootAlignedSources R N := ⟨hR,N,rfl,Q⟩
  obtain ⟨T⟩ := SharedSource.selected_realization_exists  R B
  refine ⟨Q,T,?_⟩
  intro v
  rw [←he,actualCoreResidue_source_stage]
  exact ((ownedLiteralResidueFamily (ThetaExpansion.full_product_compact_iwasawa R)).residue_selected T v).symm
end DedekindZetaZeroFree.RootDerivatives

end
