module

public import DedekindZetaZeroFree.Eisenstein.Induction.SectionContinuity
public import DedekindZetaZeroFree.Theta.Whittaker.Complex.TensorMatrixSlots

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
open NumberField Filter
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines.CanonicalStageSlot
open KPGlobalTorusFiniteStages KPGlobalResidualConstruction
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 8000000
set_option diagnostics true
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
local notation "Raw" => KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ
variable (s : RestrictedTensorSimple.Level (bad A P C))
variable (x : ∀ j : s.val, Plus A P C j.val)

theorem finiteSection_locallyConstant (q : KPFinitePlace F)
    (f : Plus A P C (Sum.inr q)) : IsLocallyConstant f.val := by
  obtain ⟨J, hJ⟩ := f.property.2
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hc : Continuous (fun y : KPLocalExceptionalConstruction.ActualCover F ζ hζ q => g⁻¹ * y) :=
    continuous_const.mul continuous_id
  have hm : ∀ᶠ y in nhds g, g⁻¹ * y ∈ J :=
    hc.continuousAt.preimage_mem_nhds (by simpa using J.isOpen.mem_nhds J.one_mem)
  filter_upwards [hm] with y hy
  have he := congrFun (hJ (g⁻¹ * y) hy) g
  simpa [KPLocalPrincipalSeries.vectorRightTranslation] using he

theorem finiteTuple_locallyConstant : IsLocallyConstant (finiteTuple A P C s x) := by
  have hl (q : s.val.toRight) : IsLocallyConstant
      (fun g : Raw => finiteTuple A P C s x g q) := by
    exact (finiteSection_locallyConstant A P C q.val
      (x ⟨Sum.inr q.val, Finset.mem_toRight.mp q.property⟩)).comp_continuous
        (QuotientGroup.continuous_mk.comp (RestrictedProduct.continuous_eval _))
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hq : ∀ q : s.val.toRight, ∀ᶠ h in nhds g,
      finiteTuple A P C s x h q = finiteTuple A P C s x g q := by
    intro q
    have h := hl q
    rw [IsLocallyConstant.iff_eventually_eq] at h
    exact h g
  filter_upwards [Filter.eventually_all.mpr hq] with h hh
  exact funext hh

theorem finiteScalar_locallyConstant : IsLocallyConstant
    (fun g : Raw => finiteScalar A P C s x g) := by
  let L := fun y : ∀ q : s.val.toRight, LocalFiber F ζ hζ P C q.val =>
    (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F ζ hζ P
      (EisensteinReferenceSections.SourceTensor.realization F ζ hζ P C
        (RestrictedTensorSimple.stageInclusion (LocalFiber F ζ hζ P C)
          (localReference F ζ hζ P C) C.exceptional (ScalarAbsorption.rightLevel C.exceptional s)
          (PiTensorProduct.tprod ℂ y)))).val.val 1
  exact (finiteTuple_locallyConstant A P C s x).comp L

theorem matrix_continuous (w : InfinitePlace F) : Continuous (matrix A w) := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  have hc : Continuous (KPLocalChartTopology.complexCoordinates F ζ hζ w) :=
    continuous_induced_dom
  have hg : Continuous (fun g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) => g.g) :=
    continuous_fst.comp hc
  have he := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (A.complex_place w)).continuous
  apply Units.continuous_iff.mpr
  constructor
  · have hv := Units.continuous_val.comp hg
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    exact he.comp ((continuous_apply j).comp ((continuous_apply i).comp hv))
  · have hv := Units.continuous_coe_inv.comp hg
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    exact he.comp ((continuous_apply j).comp ((continuous_apply i).comp hv))

theorem phase_continuous (w : InfinitePlace F) : Continuous
    (fun g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) =>
      (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ g.epsilon : ℂ)) := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  have hc : Continuous (KPLocalChartTopology.complexCoordinates F ζ hζ w) :=
    continuous_induced_dom
  exact (continuous_of_discreteTopology : Continuous (fun e : rootsOfUnity 3 F =>
    (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ e : ℂ))).comp (continuous_snd.comp hc)

theorem archComplement_continuous (w : InfinitePlace F) : Continuous
    (fun g : Raw => archComplement A P C s x g w) := by
  apply continuous_finset_prod
  intro j _
  rcases j with ⟨j, hj⟩
  cases j with
  | inr q => exact continuous_const
  | inl u =>
    by_cases hu : u = w
    · simp only [archComplement, hu, if_true]
      exact continuous_const
    · simp only [if_neg hu]
      exact ((phase_continuous A u).comp (RestrictedProduct.continuous_eval _)).mul
        ((EisensteinReferenceSections.SourceContinuity.principal_continuous positiveParameter (x ⟨Sum.inl u,hj⟩).val).comp
          ((matrix_continuous A u).comp (RestrictedProduct.continuous_eval _)))

theorem coefficient_continuous (w : InfinitePlace F) : Continuous
    (fun g : Raw => coefficient A P C s x g w) := by
  change Continuous (fun g : Raw => archComplement A P C s x g w * finiteScalar A P C s x g *
    (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (g (Sum.inl w)).epsilon : ℂ))
  exact ((archComplement_continuous A P C s x w).mul
    (finiteScalar_locallyConstant A P C s x).continuous).mul
      ((phase_continuous A w).comp (RestrictedProduct.continuous_eval _))

theorem negative_raw_joint (w : InfinitePlace F) : Continuous
    (fun p : PrincipalSeries negativeParameter × Raw => negative A P C s x p.2 w p.1) := by
  have harg : Continuous (fun p : PrincipalSeries negativeParameter × Raw =>
      (NativeStageSlot.inverse p.1, matrix A w (p.2 (Sum.inl w)))) :=
    (NativeStageSlot.inverse.continuous.comp continuous_fst).prodMk
      ((matrix_continuous A w).comp ((RestrictedProduct.continuous_eval _).comp continuous_snd))
  change Continuous (fun p : PrincipalSeries negativeParameter × Raw =>
    coefficient A P C s x p.2 w * (NativeStageSlot.inverse p.1) (matrix A w (p.2 (Sum.inl w))))
  exact ((coefficient_continuous A P C s x w).comp continuous_snd).mul
    ((KPActualReflectionData.LiteralProductPointBound.principalSeries_matrix_evaluation_joint
      positiveParameter).comp harg)

theorem negative_raw_compact_bound (w : InfinitePlace F) (K : Set Raw) (hK : IsCompact K) :
    ∃ orders : Finset ℕ, ∃ B : ℝ≥0, B ≠ 0 ∧
      ∀ (f : PrincipalSeries negativeParameter) (g : Raw), g ∈ K →
        ‖negative A P C s x g w f‖ ≤
          B * (orders.sup (chartSeminorm negativeParameter)) f := by
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn
    (coefficient_continuous A P C s x w).continuousOn
  let d : ℝ≥0 := ⟨max 0 D, le_max_left _ _⟩
  let M : Raw → ComplexGL2 := fun g => matrix A w (g (Sum.inl w))
  have hM : Continuous M := (matrix_continuous A w).comp (RestrictedProduct.continuous_eval _)
  obtain ⟨orders, B, hB, hb⟩ := NativeStageSlot.inverse_compact_bound (M '' K) (hK.image hM)
  refine ⟨orders, (1 + d) * B, by positivity, ?_⟩
  intro f g hg
  rw [negative_apply, norm_mul]
  have hv := hb f (M g) (Set.mem_image_of_mem M hg)
  have hc : ‖coefficient A P C s x g w‖ ≤ d := (hD g hg).trans (le_max_right _ _)
  have h := mul_le_mul hc hv (norm_nonneg _) d.coe_nonneg
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one]
  change ‖coefficient A P C s x g w‖ * ‖(NativeStageSlot.inverse f) (M g)‖ ≤ _
  exact h.trans (by
    have hp := mul_nonneg B.coe_nonneg (apply_nonneg (orders.sup (chartSeminorm negativeParameter)) f)
    nlinarith only [hp])

end DedekindZetaZeroFree.FourierContinuation.ComplexLines.CanonicalStageSlot

end
