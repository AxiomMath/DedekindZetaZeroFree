module

public import DedekindZetaZeroFree.Eisenstein.Induction.SectionContinuity
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RationalPeriodization.FiniteLevels

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct Topology
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology

def finitePure (s : RestrictedTensorSimple.Level (bad R P C))
    (f : ∀ p : s.val, Plus R N P C p) (p : s.val) : Plus R N P C p :=
  if p.val.isLeft then plusReference R N P C p else f p

def pureArchProduct (s : RestrictedTensorSimple.Level (bad R P C))
    (f : ∀ p : s.val, Plus R N P C p) (g : Raw R) : ℂ :=
  ∏ w, localValue R N P C (Sum.inl w) (g (Sum.inl w)) (f ⟨Sum.inl w, s.property (arch_bad R P C w)⟩)

theorem archValue_continuous (w : InfinitePlace F) (f : Plus R N P C (Sum.inl w)) :
    Continuous (fun g => localValue R N P C (Sum.inl w) g f) := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  have hc : Continuous (KPLocalChartTopology.complexCoordinates F R.A.zeta12 R.A.primitive_zeta12 w) := continuous_induced_dom
  have hm : Continuous (complexMatrix R w) := by
    have hg : Continuous (fun g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) => g.g) :=
      continuous_fst.comp hc
    have he := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).continuous
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
  have hp : Continuous (fun g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) =>
      (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12 g.epsilon : ℂ)) :=
    (continuous_of_discreteTopology : Continuous (fun e : rootsOfUnity 3 F =>
      (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12 e : ℂ))).comp (continuous_snd.comp hc)
  exact hp.mul ((EisensteinReferenceSections.SourceContinuity.principal_continuous _ f.val).comp hm)

theorem pureArchProduct_continuous (s : RestrictedTensorSimple.Level (bad R P C))
    (f : ∀ p : s.val, Plus R N P C p) : Continuous (pureArchProduct R N P C s f) := by
  apply continuous_finset_prod
  intro w _
  exact (archValue_continuous R N P C w _).comp (RestrictedProduct.continuous_eval _)

theorem scalarSource_finite_locallyConstant (x : PlusCore R N P C) :
    IsLocallyConstant (fun g : KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12 =>
      scalarSourceEvaluator R N P C x g.val) := by
  obtain ⟨U, hU⟩ := scalarSource_has_level R N P C x
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hc : Continuous (fun y : KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12 => g⁻¹ * y) :=
    continuous_const.mul continuous_id
  have he : ∀ᶠ y in nhds g, g⁻¹ * y ∈ U.toOpenSubgroup :=
    hc.continuousAt.preimage_mem_nhds (by simpa using U.toOpenSubgroup.isOpen.mem_nhds U.toOpenSubgroup.one_mem)
  filter_upwards [he] with y hy
  have hm : (g⁻¹ * y).val ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 U :=
    Subgroup.mem_map.mpr ⟨g⁻¹ * y, hy, rfl⟩
  simpa using hU g.val (g⁻¹ * y).val hm

theorem scalarSource_pure_raw_factor (s : RestrictedTensorSimple.Level (bad R P C))
    (f : ∀ p : s.val, Plus R N P C p) (g : Raw R) :
    scalarSourceEvaluator R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f))
        (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12 (amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)) =
      pureArchProduct R N P C s f g *
        scalarSourceEvaluator R N P C
          (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ (finitePure R N P C s f)))
          (EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient F R.A.zeta12 R.A.primitive_zeta12 g).val := by
  obtain ⟨G, hG⟩ := exists_reference_stage R N P C g
  let t : RestrictedTensorSimple.Level (bad R P C) :=
    ⟨s.val ∪ G.val, s.property.trans Finset.subset_union_left⟩
  have hst : s ≤ t := Finset.subset_union_left
  let h := EisensteinReferenceSections.FiniteSourceTopology.finiteProjection F R.A.zeta12 R.A.primitive_zeta12 g
  have htailg : ∀ p, p ∉ t.val → localValue R N P C p (g p) (plusReference R N P C p) = reference R P C p :=
    fun p hp => hG p (fun hg => hp (Finset.mem_union_right _ hg))
  have htailh : ∀ p, p ∉ t.val → localValue R N P C p (h p) (plusReference R N P C p) = reference R P C p := by
    intro p hp
    cases p with
    | inl w => exact False.elim (hp (t.property (arch_bad R P C w)))
    | inr q => exact htailg (Sum.inr q) hp
  let fg := fun p : t.val => extendedPlus R N P C s f p
  let fh := fun p : t.val => extendedPlus R N P C s (finitePure R N P C s f) p
  have hgins : RestrictedTensorSimple.stageInclusion (Plus R N P C) (plusReference R N P C) (bad R P C) t (PiTensorProduct.tprod ℂ fg) =
      RestrictedTensorSimple.stageInclusion (Plus R N P C) (plusReference R N P C) (bad R P C) s (PiTensorProduct.tprod ℂ f) := by
    dsimp only [fg, extendedPlus]
    rw [← RestrictedTensorSimple.insert_pure (Plus R N P C) (plusReference R N P C) s.val t.val hst f]
    exact Module.DirectLimit.of_f
  have hhins : RestrictedTensorSimple.stageInclusion (Plus R N P C) (plusReference R N P C) (bad R P C) t (PiTensorProduct.tprod ℂ fh) =
      RestrictedTensorSimple.stageInclusion (Plus R N P C) (plusReference R N P C) (bad R P C) s (PiTensorProduct.tprod ℂ (finitePure R N P C s f)) := by
    dsimp only [fh, extendedPlus]
    rw [← RestrictedTensorSimple.insert_pure (Plus R N P C) (plusReference R N P C) s.val t.val hst (finitePure R N P C s f)]
    exact Module.DirectLimit.of_f
  have hv : finiteCoreEquiv R P C (rawCoreVector R N P C g
      (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f))) =
      pureArchProduct R N P C s f g • finiteCoreEquiv R P C (rawCoreVector R N P C h
        (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ (finitePure R N P C s f)))) := by
    rw [← hgins, ← hhins, rawCoreVector_stage R N P C t g htailg,
      rawCoreVector_stage R N P C t h htailh, stageVector_pure, stageVector_pure,
      finiteCoreEquiv_stage_pure, finiteCoreEquiv_stage_pure]
    have harch : (∏ w : t.val.toLeft, localValue R N P C (Sum.inl w.val) (g (Sum.inl w.val))
        (fg ⟨Sum.inl w.val, Finset.mem_toLeft.mp w.property⟩)) = pureArchProduct R N P C s f g := by
      have he (w : t.val.toLeft) : localValue R N P C (Sum.inl w.val) (g (Sum.inl w.val))
          (fg ⟨Sum.inl w.val, Finset.mem_toLeft.mp w.property⟩) =
          localValue R N P C (Sum.inl w.val) (g (Sum.inl w.val))
            (f ⟨Sum.inl w.val, s.property (arch_bad R P C w.val)⟩) := by
        simp only [fg, extendedPlus, dif_pos (s.property (arch_bad R P C w.val))]
      simp_rw [he]
      rw [Finset.prod_coe_sort t.val.toLeft (fun w =>
        localValue R N P C (Sum.inl w) (g (Sum.inl w)) (f ⟨Sum.inl w, s.property (arch_bad R P C w)⟩))]
      rw [stage_toLeft R P C t]
      rfl
    have harchh : (∏ w : t.val.toLeft, localValue R N P C (Sum.inl w.val) (h (Sum.inl w.val))
        (fh ⟨Sum.inl w.val, Finset.mem_toLeft.mp w.property⟩)) = 1 := by
      apply Finset.prod_eq_one
      intro w _
      simp [fh, extendedPlus, finitePure, s.property (arch_bad R P C w), h,
        EisensteinReferenceSections.FiniteSourceTopology.finiteProjection, localValue, complexMatrix,
        plusReference, KPCplxPrincipalSeriesCharts.sphericalSection_one]
    rw [harch, harchh, one_smul]
    congr 2
  have hc := congrArg (fun z =>
    ((PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational
      F R.A.zeta12 R.A.primitive_zeta12 P) (finiteTensorMap R P C z)).val.val 1) hv
  simp only [map_smul] at hc
  change _ = pureArchProduct R N P C s f g *
    ((PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational
      F R.A.zeta12 R.A.primitive_zeta12 P) (finiteTensorMap R P C
        (finiteCoreEquiv R P C (rawCoreVector R N P C h
          (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ (finitePure R N P C s f))))))).val.val 1 at hc
  change (comparisonSmooth R P C (quotientCoreVector R N P C _
    (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12 (amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)))).val.val 1 =
      pureArchProduct R N P C s f g * (comparisonSmooth R P C (quotientCoreVector R N P C _
        (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12 (amalgamation F R.A.zeta12 R.A.primitive_zeta12 h)))).val.val 1
  rw [quotientCoreVector_raw, quotientCoreVector_raw]
  exact hc

theorem scalarSource_continuous (x : PlusCore R N P C) :
    Continuous (scalarSourceEvaluator R N P C x) := by
  letI : Nonempty (RestrictedTensorSimple.Level (bad R P C)) := ⟨⟨bad R P C, le_rfl⟩⟩
  obtain ⟨s, z, rfl⟩ := Module.DirectLimit.exists_of x
  change Continuous (scalarSourceEvaluator R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s z))
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    have hp : Continuous (scalarSourceEvaluator R N P C
        (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f))) := by
      apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
      apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
      change Continuous (fun g : Raw R => scalarSourceEvaluator R N P C
        (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f))
          (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12 (amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)))
      simp_rw [scalarSource_pure_raw_factor]
      exact (pureArchProduct_continuous R N P C s f).mul
        ((scalarSource_finite_locallyConstant R N P C _).continuous.comp
          (EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient_continuous F R.A.zeta12 R.A.primitive_zeta12))
    simp only [map_smul]
    change Continuous (fun g => c * scalarSourceEvaluator R N P C
      (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f)) g)
    exact continuous_const.mul hp
  | add x y hx hy => simpa only [map_add] using hx.add hy

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
