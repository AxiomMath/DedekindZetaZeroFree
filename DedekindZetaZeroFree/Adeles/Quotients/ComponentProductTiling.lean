module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdelicComponents.ArchimedeanSelector
public import DedekindZetaZeroFree.Adeles.Quotients.RationalComponents.PartialRationalTiling

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Pointwise
open MeasureTheory Function

namespace DedekindZetaZeroFree.KPActualComponentHaarSources.ProductDisintegration
open KPMsFixedHaar

open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tilingLift → tilingLift
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tilingArch → tilingArch
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tilingRational → tilingRational
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tilingLift_finite → tilingLift_finite
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tiling_arch_m → tiling_arch_m
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tiling_finite_m → tiling_finite_m
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tiling_preserve_base → tiling_preserve_base
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming actual_product_splitting → actual_product_splitting
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tiling_central_base → tiling_central_base
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tiling_orbit_base → tiling_orbit_base
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tilingRational_surjective → tilingRational_surjective
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tiling_overlap_primitive → tiling_overlap_primitive
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tilingArch_injective → tilingArch_injective
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tiling_projection_mem → tiling_projection_mem
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tiling_projection_cover → tiling_projection_cover
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tiling_quotient_invariant → tiling_quotient_invariant

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem component_measurable
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (i : Fin A.componentCount) : MeasurableSet (C F ζ hζ hF U A i) := by
  have he : C F ζ hζ hF U A i = A.components '' Set.range
      (fun y : KPCuspSiegel.OrbitQuotient F (Gi F ζ hζ hF U A i) =>
        (⟨i, y⟩ : Σ j : Fin A.componentCount,
          KPCuspSiegel.OrbitQuotient F (Gi F ζ hζ hF U A j))) := by
    ext x
    simp only [C, Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨i, y⟩, ⟨y, rfl⟩, A.components_formula i y⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, (A.components_formula i y).symm⟩
  rw [he]
  exact (A.components.isOpenMap _ isOpen_range_sigmaMk).measurableSet

private theorem finiteOrbit_measurable
    (U : Level F ζ hζ) (g : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    MeasurableSet (KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g) := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  have hs : KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g =
      ⋃ ε : rootsOfUnity 3 F,
        (fun u => KPCuspGenuineMonodromy.central F ζ hζ ε * g * u) ''
          (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) := by
    ext c
    simp only [KPCuspGenuineMonodromy.finiteOrbit, Set.mem_ofPred_eq,
      Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨ε, u, rfl⟩
      exact ⟨ε, u, u.property, rfl⟩
    · rintro ⟨ε, u, hu, rfl⟩
      exact ⟨ε, ⟨u, hu⟩, rfl⟩
  rw [hs]
  exact MeasurableSet.iUnion fun ε =>
    ((Homeomorph.mulLeft (KPCuspGenuineMonodromy.central F ζ hζ ε * g)).isOpenMap _
      U.toOpenSubgroup.isOpen).measurableSet

private theorem tiling_normalize_ae
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (i : Fin A.componentCount)
    (D : Set (KPSmoothActualFlowData.GInfinity F))
    (a : KPSmoothActualFlowData.GInfinity F)
    (ha : ∃ γ : Ga F ζ hζ hF U A i, γ.val * a ∈ D)
    (b : KPFiniteCuspAtlas.FiniteCover F ζ hζ) (hb : b ∈ B F ζ hζ hF U A i) :
    ∃ δ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ,
      δ.val * m F ζ hζ (a,b) ∈ m F ζ hζ '' (D ×ˢ B F ζ hζ hF U A i) := by
  obtain ⟨γ,hγ⟩ := ha
  obtain ⟨δ,hδ,he⟩ := γ.property
  let δ' : Gi F ζ hζ hF U A i := ⟨δ,hδ⟩
  obtain ⟨e,heq⟩ := actual_product_splitting F ζ hζ
  obtain ⟨⟨v,c⟩,hc⟩ := e.surjective (tilingLift F ζ hζ δ * m F ζ hζ (a,b))
  have hc' : m F ζ hζ (v,c) = tilingLift F ζ hζ δ * m F ζ hζ (a,b) :=
    (heq v c).symm.trans hc
  have hv := congrArg (KPSmoothLocalQuotientCharts.archProjection F ζ hζ) hc'
  rw [tiling_arch_m,map_mul,tiling_arch_m] at hv
  have hbase := congrArg (KPCuspGenuineMonodromy.finiteProjection F ζ hζ) hc'
  rw [tiling_finite_m,map_mul,tilingLift_finite,tiling_finite_m] at hbase
  have hcb : c ∈ B F ζ hζ hF U A i :=
    tiling_preserve_base F ζ hζ U (A.representative i) b c δ' hb hbase
  refine ⟨tilingRational F ζ hζ δ, ⟨(v,c), ⟨?_,hcb⟩,hc'⟩⟩
  change tilingArch F ζ hζ δ = γ.val at he
  change v ∈ D
  change v = tilingArch F ζ hζ δ * a at hv
  rw [hv,he]
  exact hγ

private theorem ae_domain_no_overlap {H X : Type*} [Group H] [Countable H]
    [MulAction H X] [MeasurableSpace X] (μ : Measure X) (D : Set X)
    (hD : IsFundamentalDomain H D μ) :
    ∀ᵐ x ∂μ, ∀ α : H, x ∈ D → α • x ∈ D → α = 1 := by
  apply ae_all_iff.mpr
  intro α
  by_cases hα : α = 1
  · exact Filter.Eventually.of_forall fun _ _ _ => hα
  have hd := hD.aedisjoint (show α⁻¹ ≠ 1 by simpa using hα)
  have hn : ∀ᵐ x ∂μ, x ∉ α⁻¹ • D ∩ D := measure_eq_zero_iff_ae_notMem.mp (by simpa only [one_smul] using hd.eq)
  filter_upwards [hn] with x hx hxD hαx
  exact False.elim (hx ⟨Set.mem_smul_set.mpr ⟨α • x, hαx, by simp⟩, hxD⟩)

theorem product_domain_partial_fundamental
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (i : Fin A.componentCount)
    (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) [ν.IsHaarMeasure]
    (hproduct : Measure.map (m F ζ hζ) (R.archHaar.prod ν) = R.adelicHaar)
    (D : Set (KPSmoothActualFlowData.GInfinity F))
    (hDm : MeasurableSet D)
    (hD : IsFundamentalDomain (Ga F ζ hζ hF U A i) D R.archHaar) :
    MeasurableSet (P.projection U ⁻¹' C F ζ hζ hF U A i) ∧
    MeasurableSet (m F ζ hζ '' (D ×ˢ B F ζ hζ hF U A i)) ∧
    m F ζ hζ '' (D ×ˢ B F ζ hζ hF U A i) ⊆
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ ⁻¹'
        (P.projection U ⁻¹' C F ζ hζ hF U A i) ∧
    IsFundamentalDomain (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ)
      (m F ζ hζ '' (D ×ˢ B F ζ hζ hF U A i))
      (R.adelicHaar.restrict (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ ⁻¹'
        (P.projection U ⁻¹' C F ζ hζ hF U A i))) := by
  letI := R.arch_isHaar
  letI := R.adelic_isHaar
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := ActualQuotient.actual_cover_secondCountable F ζ hζ
  obtain ⟨e, he⟩ := actual_product_splitting F ζ hζ
  letI : LocallyCompactSpace (KPSmoothActualFlowData.GInfinity F ×
      KPFiniteCuspAtlas.FiniteCover F ζ hζ) := e.isClosedEmbedding.locallyCompactSpace
  letI : LocallyCompactSpace (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    (isOpenQuotientMap_snd (X := KPSmoothActualFlowData.GInfinity F)).locallyCompactSpace
  letI : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F ×
      KPFiniteCuspAtlas.FiniteCover F ζ hζ) := e.toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F) :=
    (isEmbedding_prodMkLeft (1 : KPFiniteCuspAtlas.FiniteCover F ζ hζ)).secondCountableTopology
  letI : SecondCountableTopology (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    (isEmbedding_prodMkRight (1 : KPSmoothActualFlowData.GInfinity F)).secondCountableTopology
  letI : BorelSpace (KPSmoothActualFlowData.GInfinity F) := ⟨rfl⟩
  letI : Countable (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) := by
    have hΓ := ActualQuotient.actual_rational_closed_discrete F ζ hζ
    exact (IsLindelof.countable_of_isDiscrete hΓ.1.isLindelof hΓ.2).to_subtype
  letI : Countable (Ga F ζ hζ hF U A i) := by
    obtain ⟨hc, hd, _⟩ := actual_component_arch_group_selector F ζ hζ hF U A i
    exact (hc.isLindelof.countable_of_isDiscrete
      (SetLike.isDiscrete_iff_discreteTopology.mpr hd)).to_subtype
  have hem : MeasurableEmbedding (m F ζ hζ) := by
    have heq : m F ζ hζ = e := by
      funext p
      exact (he p.1 p.2).symm
    rw [heq]
    exact e.toHomeomorph.measurableEmbedding
  have hTm : MeasurableSet (P.projection U ⁻¹' C F ζ hζ hF U A i) :=
    (component_measurable F ζ hζ hF U A i).preimage (P.continuous U).measurable
  have hT : MeasurableSet (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ ⁻¹'
      (P.projection U ⁻¹' C F ζ hζ hF U A i)) :=
    hTm.preimage (show Continuous (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ)
      from continuous_quot_mk).measurable
  have hSm : MeasurableSet (m F ζ hζ '' (D ×ˢ B F ζ hζ hF U A i)) :=
    hem.measurableSet_image.mpr
      (hDm.prod (finiteOrbit_measurable F ζ hζ U (A.representative i)))
  let good := fun a : KPSmoothActualFlowData.GInfinity F =>
    (∃ α : Ga F ζ hζ hF U A i, α.val * a ∈ D) ∧
      ∀ α : Ga F ζ hζ hF U A i, a ∈ D → α.val * a ∈ D → α = 1
  have hgood : ∀ᵐ a ∂ R.archHaar, good a :=
    hD.ae_covers.and (ae_domain_no_overlap R.archHaar D hD)
  have hgoodAdelic : ∀ᵐ x ∂ R.adelicHaar,
      good (KPSmoothLocalQuotientCharts.archProjection F ζ hζ x) := by
    rw [← hproduct, hem.ae_map_iff]
    have hp := (Measure.quasiMeasurePreserving_fst (μ := R.archHaar) (ν := ν)).ae hgood
    filter_upwards [hp] with x hx
    rcases x with ⟨a, b⟩
    simpa only [tiling_arch_m] using hx
  have hgoodTrans : ∀ᵐ x ∂ R.adelicHaar,
      ∀ δ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ,
        good (KPSmoothLocalQuotientCharts.archProjection F ζ hζ (δ.val * x)) := by
    apply ae_all_iff.mpr
    intro δ
    exact (measurePreserving_mul_left R.adelicHaar δ.val).quasiMeasurePreserving.ae hgoodAdelic
  refine ⟨hTm, hSm, ?_, hSm.nullMeasurableSet, ?_, ?_⟩
  · rintro x ⟨⟨a,b⟩, ⟨ha,hb⟩, rfl⟩
    exact tiling_projection_mem F ζ hζ U P (A.representative i) b a hb
  · apply (ae_restrict_iff' hT).mpr
    filter_upwards [hgoodTrans] with x hx hxT
    obtain ⟨⟨a,c⟩, hc⟩ := e.surjective x
    have he' : m F ζ hζ (a,c) = x := (he a c).symm.trans hc
    rw [← he'] at hxT ⊢
    obtain ⟨δ,u,hδ⟩ := tiling_projection_cover F ζ hζ U P (A.representative i) c a hxT
    obtain ⟨⟨v,b⟩,hb⟩ := e.surjective
      (tilingLift F ζ hζ δ * m F ζ hζ (a,c))
    have hb' : m F ζ hζ (v,b) = tilingLift F ζ hζ δ * m F ζ hζ (a,c) :=
      (he v b).symm.trans hb
    have hbase := congrArg (KPCuspGenuineMonodromy.finiteProjection F ζ hζ) hb'
    rw [tiling_finite_m,map_mul,tilingLift_finite,tiling_finite_m] at hbase
    have hbB : b ∈ B F ζ hζ hF U A i :=
      (tiling_orbit_base F ζ hζ U (A.representative i) b).mpr ⟨u,hbase.trans hδ⟩
    have hv : good v := by
      have hg := hx (tilingRational F ζ hζ δ)
      change good (KPSmoothLocalQuotientCharts.archProjection F ζ hζ
        (tilingLift F ζ hζ δ * x)) at hg
      rw [← he', ← hb', tiling_arch_m] at hg
      exact hg
    obtain ⟨ρ,hρ⟩ := tiling_normalize_ae F ζ hζ hF U A i D v hv.1 b hbB
    rw [hb'] at hρ
    refine ⟨ρ * tilingRational F ζ hζ δ, ?_⟩
    change (ρ.val * tilingLift F ζ hζ δ) * m F ζ hζ (a,c) ∈ _
    simpa only [mul_assoc] using hρ
  · intro γ η hne
    apply measure_eq_zero_iff_ae_notMem.mpr
    have hg := ae_restrict_of_ae (s := KPSmoothLocalQuotientCharts.quotientMap F ζ hζ ⁻¹'
      (P.projection U ⁻¹' C F ζ hζ hF U A i)) hgoodTrans
    filter_upwards [hg] with x hx hxBoth
    obtain ⟨y,hyS,hye⟩ := Set.mem_smul_set.mp hxBoth.1
    obtain ⟨z,hzS,hze⟩ := Set.mem_smul_set.mp hxBoth.2
    have heq := hze.trans hye.symm
    obtain ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩ := hyS
    obtain ⟨⟨v,c⟩,⟨hv,hc⟩,rfl⟩ := hzS
    have hga : good a := by
      have hg := hx γ⁻¹
      change good (KPSmoothLocalQuotientCharts.archProjection F ζ hζ (γ.val⁻¹ * x)) at hg
      change γ.val * m F ζ hζ (a,b) = x at hye
      rw [← hye, inv_mul_cancel_left, tiling_arch_m] at hg
      exact hg
    obtain ⟨δ,rfl⟩ := tilingRational_surjective F ζ hζ γ
    obtain ⟨θ,rfl⟩ := tilingRational_surjective F ζ hζ η
    have hh : tilingLift F ζ hζ (θ⁻¹ * δ) * m F ζ hζ (a,b) =
        m F ζ hζ (v,c) := by
      change tilingLift F ζ hζ θ * m F ζ hζ (v,c) =
        tilingLift F ζ hζ δ * m F ζ hζ (a,b) at heq
      rw [map_mul,map_inv,mul_assoc, ← heq]
      group
    have hhf := congrArg (KPCuspGenuineMonodromy.finiteProjection F ζ hζ) hh
    rw [map_mul,tilingLift_finite,tiling_finite_m,tiling_finite_m] at hhf
    have hδ : θ⁻¹ * δ ∈ Gi F ζ hζ hF U A i :=
      tiling_overlap_primitive F ζ hζ U (A.representative i) b c _ hb hc hhf
    let α : Ga F ζ hζ hF U A i :=
      ⟨tilingArch F ζ hζ (θ⁻¹ * δ), ⟨θ⁻¹ * δ,hδ,rfl⟩⟩
    have hha := congrArg (KPSmoothLocalQuotientCharts.archProjection F ζ hζ) hh
    rw [map_mul,tiling_arch_m,tiling_arch_m] at hha
    have hα : α.val * a ∈ D := by
      change KPSmoothLocalQuotientCharts.archProjection F ζ hζ
        (tilingLift F ζ hζ (θ⁻¹ * δ)) * a ∈ D
      rw [hha]
      exact hv
    have hα1 : α = 1 := hga.2 α ha hα
    have harch : tilingArch F ζ hζ (θ⁻¹ * δ) = tilingArch F ζ hζ 1 := by
      simpa [α] using congrArg Subtype.val hα1
    have hr : θ⁻¹ * δ = 1 := tilingArch_injective F ζ hζ harch
    have hδθ : δ = θ := by
      have hh' := congrArg (fun k => θ * k) hr
      simpa [mul_assoc] using hh'
    exact hne (congrArg (tilingRational F ζ hζ) hδθ)

end DedekindZetaZeroFree.KPActualComponentHaarSources.ProductDisintegration

end
