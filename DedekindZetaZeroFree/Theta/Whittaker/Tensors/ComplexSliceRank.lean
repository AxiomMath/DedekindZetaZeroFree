module

public import DedekindZetaZeroFree.Theta.Whittaker.CompletedPeriodCovariance
public import DedekindZetaZeroFree.Theta.Whittaker.Tensors.ComplexSlices

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources ThetaExpansion TensorActionSource
open KPCplxActualImage KPCplxWhittakerUnique
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

theorem canonicalComplexSlice_whittaker
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀j : s.val,actualLocal R H j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val) :
    ∃L : KPCplxActualImage.Theta ComplexLines.traceFrequency →L[ℂ] ℂ,
      L ∈ whittakerSpace ComplexLines.traceFrequency ComplexLines.traceCharacter ∧
      ∀v : KPGlobalResidualConstruction.complexCore,
      L (ComplexLines.harmonicInclusion v) =
        canonicalComplexSlice R P C μ hμ  hR N hC u hspherical hx s x w hw 1 v := by
  obtain ⟨y,hy⟩ := canonicalComplexSlice_source_lift R P C μ hμ  hR N hC u hspherical hx s x w hw
  refine ⟨ComplexLines.actualWhittakerExtension R N P C  s y w hw,
    ComplexLines.actualWhittakerExtension_mem R N P C  s y w hw,?_⟩
  intro v
  exact (ComplexLines.actualWhittakerExtension_core R N P C  s y w hw v).trans (hy 1 v).symm

theorem canonicalCovariantNative_slice_le (w : InfinitePlace F) :
    (HC).sliceLine (Sum.inl w) ≤ ComplexLines.traceLine := by
  apply Submodule.span_le.mpr
  rintro l ⟨s,x,hw,rfl⟩
  obtain ⟨L,hL,he⟩ := canonicalComplexSlice_whittaker R P C μ hμ  hR N hC u hspherical hx s x w hw
  apply ComplexLines.mem_traceLine_of_extension _ L hL
  intro v
  convert he v using 1 <;> simp only [canonicalComplexSlice,MultilinearMap.toLinearMap_apply]
  apply congrArg _
  funext j
  by_cases hj : j = ⟨Sum.inl w,hw⟩
  · subst j
    simp
  · simp [hj]

theorem canonicalCovariantNative_complex_rank (w : InfinitePlace F) :
    Module.rank ℂ ((HC).sliceLine (Sum.inl w)) ≤ 1 := by
  apply ComplexLines.slice_rank_of_extensions (HC) w
  intro s x hw
  obtain ⟨L,hL,he⟩ := canonicalComplexSlice_whittaker R P C μ hμ  hR N hC u hspherical hx s x w hw
  refine ⟨L,hL,?_⟩
  intro v
  convert he v using 1 <;> simp only [canonicalComplexSlice,MultilinearMap.toLinearMap_apply]
  apply congrArg _
  funext j
  by_cases hj : j = ⟨Sum.inl w,hw⟩
  · subst j
    simp
  · simp [hj]

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
