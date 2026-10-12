module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.RestrictedEvaluationCompactBounds
public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.SourceCompactBounds
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteAverages.CompactAnchorLifts
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.BoundaryPairings.FiniteSumBound

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open MomentSources KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12

include N in
theorem restrictedSlot_boundary_pair_bound
    (HR : KPSmoothLocalQuotientCharts.HaarRecipe F R.A.zeta12 R.A.primitive_zeta12)
    (HP : KPMsFixedHaarDisintegration.SphericalTransport F R.A.zeta12 R.A.primitive_zeta12)

    (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
    (x : ∀j : s.val, LiteralSource.Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val)
    (U : Level F ζ hζ)
    (dk : Measure (KPMsGreenFlux.K F)) [IsProbabilityMeasure dk] :
    ∃orders : Finset ℕ, ∃B : ℝ, 0 < B ∧ ∀v : complexCore,
      ‖LiteralSource.finiteBoundaryPair R HR HP U dk
        (LiteralSource.quotientCoreEvaluator R.A P C (restrictedSlotTensor R.A P C s x w hw v))
        (LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v))‖ ≤
        B * ((orders.sup coreSeminorm) v)^2 := by
  obtain ⟨K,hK,hlift⟩ := ResidualFiniteAnchor.exists_compact_raw_anchors F ζ hζ
    (fun j => (KPBoundedCuspFrames.actualFiniteRepresentative
      (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) U) j).val)
  obtain ⟨os,Bs,hBs,hs⟩ := restrictedSlot_source_compact_bound R P C s x w hw K hK
  obtain ⟨ot,Bt,hBt,ht⟩ := restrictedSlot_upper_compact_bound R N P C  s x w hw K hK
  let orders := os ∪ ot
  let mass := (nativeDisintegration F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) U).beta.real Set.univ
  let coeff : ℝ := (Bs:ℝ)*(Bt:ℝ)*mass
  have hmass : 0 ≤ mass := ENNReal.toReal_nonneg
  have hc : 0 ≤ coeff := mul_nonneg (mul_nonneg Bs.coe_nonneg Bt.coe_nonneg) hmass
  refine ⟨orders,coeff+1,by positivity,?_⟩
  intro v
  have hps : (os.sup coreSeminorm) v ≤ (orders.sup coreSeminorm) v :=
    (Finset.sup_mono (f:=coreSeminorm) Finset.subset_union_left) v
  have hpt : (ot.sup coreSeminorm) v ≤ (orders.sup coreSeminorm) v :=
    (Finset.sup_mono (f:=coreSeminorm) Finset.subset_union_right) v
  have hb := LiteralSource.finiteBoundaryPair_bound R HR HP U dk
    (LiteralSource.quotientCoreEvaluator R.A P C (restrictedSlotTensor R.A P C s x w hw v))
    (LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v))
    ((Bs:ℝ)*(orders.sup coreSeminorm) v) ((Bt:ℝ)*(orders.sup coreSeminorm) v)
    (mul_nonneg Bs.coe_nonneg (apply_nonneg _ _))
    (by
      intro j k
      obtain ⟨a,ha,he⟩ := hlift j k
      have hh := hs v a ha
      change ‖LiteralSource.quotientCoreEvaluator R.A P C
        (restrictedSlotTensor R.A P C s x w hw v)
        (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ a))‖ ≤ _ at hh
      rw [he] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left hps Bs.coe_nonneg))
    (by
      intro j k
      obtain ⟨a,ha,he⟩ := hlift j k
      have hh := ht v a ha
      rw [he] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left hpt Bt.coe_nonneg))
  apply hb.trans
  change (Bs:ℝ)*(orders.sup coreSeminorm) v * ((Bt:ℝ)*(orders.sup coreSeminorm) v) * mass ≤
    (coeff+1)*((orders.sup coreSeminorm) v)^2
  dsimp only [coeff]
  nlinarith [sq_nonneg ((orders.sup coreSeminorm) v)]

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
