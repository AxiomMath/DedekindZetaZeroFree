module

public import DedekindZetaZeroFree.Theta.Periods.TensorInsertionAndExtension
public import DedekindZetaZeroFree.Theta.Whittaker.Tensors.LocalCovariance
public import DedekindZetaZeroFree.Theta.Whittaker.Tensors.CovariantExtension
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.LocalEvaluations
public import DedekindZetaZeroFree.Theta.Periods.RepeatedCorePeriod
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.Injectivity
public import DedekindZetaZeroFree.Eisenstein.Residues.LieActionComparison

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

include μ hμ in
def canonicalCovariantNative
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
    NonDegenerate.ComplexCovariant R N := by
  let t : RestrictedTensorSimple.Level (bad R.A P C) := ⟨bad R.A P C,le_rfl⟩
  let x := RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C)
    (bad R.A P C) t (PiTensorProduct.tprod ℂ u)
  let Q := repeatedCoreSources R P C x hspherical
  let S05 : JointRootAlignedSources R N := ⟨hR,N,rfl,Q⟩
  let T := Classical.choice (SharedSource.selected_realization_exists  R S05)
  have hD : ∀ v, T.theta v = coreResidue R P C x := by
    intro v
    exact ((ownedLiteralResidueFamily (full_product_compact_iwasawa R)).residue_selected T v).symm
  let D : NonDegenerate.PeriodSource R N := {
    toJointRealizedFlatSources := ⟨S05,T⟩
    probe := 1
    coefficient := fourier R Q.dq (T.theta 1) 1
    coefficient_ne := by rw [hD]; exact hx
    period_limit := fourier_residue_tendsto T 1 1 }
  let y : ∀ j : t.val, MomentSources.actualLocal R (actualImageData R P C μ hμ) j.val :=
    fun j => TensorActionSource.sourceQuotient R (actualImageData R P C μ hμ) j.val (u j)
  have hy : TensorActionSource.sourceStageQuotient R (actualImageData R P C μ hμ)
      t.val (PiTensorProduct.tprod ℂ u) = PiTensorProduct.tprod ℂ y :=
    PiTensorProduct.map_tprod _ u
  let B : NonDegenerate.Faithful R N := {
    toDictionary := {
      toPeriodSource := D
      finiteData := actualImageData R P C μ hμ
      references := actualReference R P C μ hμ
      bad := bad R.A P C
      bad_exact := by
        intro p
        cases p <;> simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad,hC]
      scalarSlot := TensorSeedSource.scalarSlot R
      coreMap := actualCoreResidue R P C μ hμ N
      selected := fun _ => RestrictedTensorSimple.stageInclusion _ _ _ t (PiTensorProduct.tprod ℂ y)
      selected_eq := by
        intro v
        rw [← hy,actualCoreResidue_source_stage]
        exact (hD v).symm
      selected_frozen_stage := fun _ => ⟨t,y,rfl,rfl⟩ }
    core_injective := actualCoreResidue_injective R P C μ hμ N hC
    regular := actualCoreResidue_regular R P C μ hμ N }
  have hn : HCGeneration.NativeSlotComparisons B :=
    actualCoreResidue_native_slots R P C μ hμ N
  let G := HCGeneration.faithfulGeneratedOfNativeSlots B hn
  let Df := CovariantAssembly.add_finite G (by
    dsimp only [G, HCGeneration.faithfulGeneratedOfNativeSlots, B]
    exact actual_finite_covariance R P C μ hμ N)
  let DC := CovariantAssembly.add_complex Df (by
    dsimp only [Df, CovariantAssembly.add_finite, G, HCGeneration.faithfulGeneratedOfNativeSlots, B]
    exact actual_complex_covariance R P C μ hμ N)
  exact DC

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

theorem canonicalCovariantNative_native :
    RootDerivatives.NativeLieComparison R (DC).finiteData (DC).references (DC).bad (DC).coreMap := by
  change RootDerivatives.NativeLieComparison R (actualImageData R P C μ hμ)
    (actualReference R P C μ hμ) (bad R.A P C) (actualCoreResidue R P C μ hμ N)
  exact RootDerivatives.actualCoreResidue_nativeLie R P C μ hμ N

def canonicalComplexSlice (s : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀j : s.val,actualLocal R H j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val) (g : Group R) :
    KPGlobalResidualConstruction.complexCore →ₗ[ℂ] ℂ :=
  (coreStageMultilinear (actualLocal R (HC).finiteData) (HC).references (HC).bad
    ((HC).literalPeriod g) s).toLinearMap x ⟨Sum.inl w,hw⟩

theorem canonicalComplexSlice_source_lift
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀j : s.val,actualLocal R H j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val) :
    ∃y : ∀j : s.val,Plus R.A P C j.val, ∀g : Group R,
      ∀v : KPGlobalResidualConstruction.complexCore,
      canonicalComplexSlice R P C μ hμ  hR N hC u hspherical hx s x w hw g v =
        ComplexLines.restrictedSlotPeriod R P C s y w hw g v := by
  obtain ⟨y,hy⟩ := ComplexLines.actualSlot_period_lift R P C μ hμ N s x w hw
  exact ⟨y,hy⟩

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
