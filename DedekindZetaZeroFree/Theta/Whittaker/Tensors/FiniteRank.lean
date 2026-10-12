module

public import DedekindZetaZeroFree.Theta.Whittaker.Tensors.JointArchimedeanExterior
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.LocalTensorRank
public import DedekindZetaZeroFree.Theta.Whittaker.FinitePlaces.CoefficientRankBound
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.Wild.DetectedTensorVectors

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
set_option maxHeartbeats 2000000
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)

variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)

variable
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
        ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ u))) 1 ≠ 0)

local notation "DC" => canonicalCovariantNative R P C μ hμ  hR N hC u hspherical hx
set_option quotPrecheck false
local notation "HC" => (DC).toGenerated.tensorHC
local notation "H" => actualImageData R P C μ hμ

open KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod WildCurrentGlobalMap
open WildFiniteExteriorAssembly KPAdelicCoverRestrictedProduct
local notation "D" => (DC).tensorDetected.toTensorActions

theorem canonicalFinite_coefficient_rank (T : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level (D).bad) (hT : places T ⊆ s.val)
    (x : ∀j : s.val,actualLocal R (D).finiteData j)
    (hdet : coreStageMultilinear _ (D).references (D).bad ((D).toTensorHC.literalPeriod 1) s x ≠ 0)
    (ht : ∀q : KPFinitePlace F, Sum.inr q ∉ places T → WildCurrentTameExterior.tameSlot (Sum.inr q))
    (q : T) : Module.rank ℂ (ActualKirillov.coefficient F R.A.zeta12 R.A.primitive_zeta12 q.val
      ((D).finiteData q.val).inducing ((D).finiteData q.val).inducing.polarization
      ((D).finiteData q.val).haar ((D).finiteData q.val).haar_integer) ≤ 1 := by
  have hJ := canonicalJointForm_injective R P C μ hμ  hR N hC u hspherical hx T s hT x hdet ht q
  have hd : WildCurrentJointForm.jointForm (D) T s hT x
      (PiTensorProduct.tprod ℂ (detectedJacquetTuple (D) T s hT x))≠0 := by
    rw [detectedJacquet_pure]
    exact hdet
  exact WildTensorRankPure.local_rank_le_one_of_detected
    (Jacquet F R.A.zeta12 R.A.primitive_zeta12 T (character T) (fiber (D) T) (action (D) T))
    (detectedJacquetTuple (D) T s hT x) (WildCurrentJointForm.jointForm (D) T s hT x) hJ hd q

theorem canonicalFinite_slice_rank (T : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level (D).bad) (hT : places T ⊆ s.val)
    (x : ∀j : s.val,actualLocal R (D).finiteData j)
    (hdet : coreStageMultilinear _ (D).references (D).bad ((D).toTensorHC.literalPeriod 1) s x ≠ 0)
    (ht : ∀q : KPFinitePlace F, Sum.inr q ∉ places T → WildCurrentTameExterior.tameSlot (Sum.inr q))
    (q : T) : Module.rank ℂ ((D).toTensorHC.sliceLine (Sum.inr q.val))≤1 := by
  exact TensorActions.finite_slice_rank_le_one_of_coefficient_rank (D) q.val
    (canonicalFinite_coefficient_rank R P C μ hμ  hR N hC u hspherical hx T s hT x hdet ht q)
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
