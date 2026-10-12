module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspCoordinates.AngularMeasurableDescent
public import DedekindZetaZeroFree.Metaplectic.Cubic.Quotients.HaarLocalFiniteness

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree.FullAngularHaar.Constructor.JointMeasure

open KPCompactStabilizerHaarSources
attribute [local instance] KPCompactStabilizerHaarSources.groupMeasurableSpace
  KPCompactStabilizerHaarSources.groupBorelSpace
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming archEquiv → archEquiv
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming basepoint_eq → basepoint_eq

set_option backward.isDefEq.respectTransparency false in
private theorem original_full_K (d : ℕ) (μ : Measure (G d)) [μ.IsHaarMeasure] :
    ∃ (e : G d ≃ₜ (X d × K d)) (c : ℝ≥0), 0 < c ∧
      (∀ g, (e g).1 = g • o d) ∧
      (∀ x k, e.symm (x, k) =
        KPArithmeticAction.productProjectiveSection d x * (k : G d)) ∧
      Measure.map e μ =
        (c : ℝ≥0∞) • ((KPArch.hyperbolicVolume d).prod (stabilizerHaar d)) := by
  obtain ⟨e, heOrbit, heFiber⟩ := product_iwasawa_homeomorph d
  obtain ⟨hfinite, hpositive, hinvariant⟩ := hyperbolic_volume_properties d
  let ν : Measure (G d) :=
    Measure.map e.symm ((KPArch.hyperbolicVolume d).prod (stabilizerHaar d))
  have : ν.IsHaarMeasure := compact_fiber_lift_isHaar d e heFiber
    (KPArch.hyperbolicVolume d) hfinite hpositive hinvariant
    (stabilizerHaar d) inferInstance inferInstance
  refine ⟨e, Measure.haarScalarFactor μ ν,
    Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν, heOrbit, heFiber, ?_⟩
  calc
    Measure.map e μ = Measure.map e (Measure.haarScalarFactor μ ν • ν) :=
      congrArg (Measure.map e) (Measure.isMulLeftInvariant_eq_smul μ ν)
    _ = (Measure.haarScalarFactor μ ν : ℝ≥0∞) • Measure.map e ν :=
      Measure.map_smul _ e.measurable.aemeasurable
    _ = _ := by
      congr 1
      dsimp [ν]
      rw [Measure.map_map e.measurable e.symm.measurable]
      simp only [e.apply_symm_apply, Function.comp_def, Measure.map_id']

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

set_option backward.isDefEq.respectTransparency false in
private theorem original_recipe_full_K
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) :
    ∃ (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
        (X (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
      (c : ℝ≥0), 0 < c ∧
      (∀ g, (e g).1 = KPMsFixedHaarDisintegration.archBasepoint F g) ∧
      (∀ x k i, (e.symm (x, k)) (KPCusp.complexPlace F i) =
        (KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
          (k : G (KPCuspLogShape.dimension F))) i) ∧
      Measure.map e R.archHaar = (c : ℝ≥0∞) •
        ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).prod
          (stabilizerHaar (KPCuspLogShape.dimension F))) := by
  let : BorelSpace (KPSmoothActualFlowData.GInfinity F) := ⟨rfl⟩
  let := R.arch_isHaar
  let a := archEquiv F ζ hζ
  let : (Measure.map a R.archHaar).IsHaarMeasure := a.isHaarMeasure_map R.archHaar
  obtain ⟨e, c, hc, heOrbit, heFiber, he⟩ := original_full_K
    (KPCuspLogShape.dimension F) (Measure.map a R.archHaar)
  refine ⟨a.toHomeomorph.trans e, c, hc, ?_, ?_, ?_⟩
  · intro g
    exact (heOrbit (a g)).trans (basepoint_eq F ζ hζ g).symm
  · intro x k i
    have hf : a ((a.toHomeomorph.trans e).symm (x, k)) =
        KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
          (k : G (KPCuspLogShape.dimension F)) := by
      change a (a.symm (e.symm (x, k))) = _
      rw [a.apply_symm_apply]
      exact heFiber x k
    exact congrFun hf i
  · have ha : Measurable (fun g => a g) := a.continuous.measurable
    rw [Measure.map_map e.measurable ha] at he
    exact he

open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming rationalArch → rationalArch
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming subgroupEquiv → subgroupEquiv
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming rationalArch_equivariant → rationalArch_equivariant
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming basepoint_continuous → basepoint_continuous
open KPActualComponentHaarSources

set_option backward.isDefEq.respectTransparency false in

private theorem actual_atlas_group_domain
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : KPMsFixedHaar.Level F ζ hζ)
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (i : Fin A.componentCount) :
    IsFundamentalDomain (Ga F ζ hζ hF U A i)
      (KPMsFixedHaarDisintegration.archBasepoint F ⁻¹'
        (A.cuspAtlas i).fundamentalDomain) R.archHaar := by
  obtain ⟨e,c,hc,heBase,heFiber,heMap⟩ := original_recipe_full_K R
  let : IsFiniteMeasureOnCompacts (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) :=
    (hyperbolic_volume_properties (KPCuspLogShape.dimension F)).1
  have hfst : Measure.map (KPMsFixedHaarDisintegration.archBasepoint F) R.archHaar =
      (c : ℝ≥0∞) • KPArch.hyperbolicVolume (KPCuspLogShape.dimension F) := by
    have hfun : KPMsFixedHaarDisintegration.archBasepoint F = Prod.fst ∘ e :=
      funext fun g => (heBase g).symm
    rw [hfun, ← Measure.map_map measurable_fst e.measurable, heMap,
      Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_fst_prod]
    simp
  have hb := (basepoint_continuous F ζ hζ).measurable
  have hqmp : Measure.QuasiMeasurePreserving (KPMsFixedHaarDisintegration.archBasepoint F)
      R.archHaar (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) :=
    ⟨hb, by rw [hfst]; exact Measure.smul_absolutelyContinuous⟩
  exact (A.cuspAtlas i).isFundamentalDomain.preimage_of_equiv hqmp
    (subgroupEquiv F ζ hζ hF U A i).bijective
    (fun γ g => rationalArch_equivariant F ζ hζ γ g)

open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tilingLift → tilingLift
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tiling_arch_m → tiling_arch_m
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tiling_finite_m → tiling_finite_m
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tilingLift_finite → tilingLift_finite
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tiling_preserve_base → tiling_preserve_base

 theorem actual_rational_finite_fiber
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : KPMsFixedHaar.Level F ζ hζ)
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (i : Fin A.componentCount)
    (γ : Gi F ζ hζ hF U A i)
    (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) [ν.IsHaarMeasure] :
    ∃ d : KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      (∀ a b, tilingLift F ζ hζ γ.val * m F ζ hζ (a,b) =
        m F ζ hζ (rationalArch F ζ hζ γ.val * a, d*b)) ∧
      (fun b => d*b) ⁻¹' B F ζ hζ hF U A i = B F ζ hζ hF U A i ∧
      MeasurePreserving (fun b => d*b)
        (ν.restrict (B F ζ hζ hF U A i)) (ν.restrict (B F ζ hζ hF U A i)) := by
  obtain ⟨e,he⟩ := actual_product_splitting F ζ hζ
  have hem : ∀ p, e p = m F ζ hζ p := fun p => he p.1 p.2
  let d := (e.symm (tilingLift F ζ hζ γ.val)).2
  have ha : (e.symm (tilingLift F ζ hζ γ.val)).1 = rationalArch F ζ hζ γ.val := by
    have hh := congrArg (KPSmoothLocalQuotientCharts.archProjection F ζ hζ)
      (e.apply_symm_apply (tilingLift F ζ hζ γ.val))
    rw [hem, tiling_arch_m] at hh
    exact hh
  have hmul : ∀ a b, tilingLift F ζ hζ γ.val * m F ζ hζ (a,b) =
      m F ζ hζ (rationalArch F ζ hζ γ.val * a,d*b) := by
    intro a b
    rw [← e.apply_symm_apply (tilingLift F ζ hζ γ.val), ← hem (a,b), ← map_mul]
    change e ((e.symm (tilingLift F ζ hζ γ.val)).1 * a, d*b) = _
    rw [ha,hem]
  have hd : KPCuspGenuineMonodromy.finiteBase F ζ hζ d =
      KPFiniteComponents.diagonal F γ.val := by
    have hh := congrArg (KPCuspGenuineMonodromy.finiteProjection F ζ hζ) (hmul 1 1)
    rw [tiling_finite_m,map_mul,tilingLift_finite,tiling_finite_m] at hh
    simpa only [map_one,mul_one] using hh.symm
  have hpre : (fun b => d*b) ⁻¹' B F ζ hζ hF U A i = B F ζ hζ hF U A i := by
    ext b
    constructor
    · intro hb
      have hh := tiling_preserve_base F ζ hζ U (A.representative i)
        (d*b) b γ⁻¹ hb (by
          simp only [map_mul,map_inv,hd,Subgroup.coe_inv,inv_mul_cancel_left])
      exact hh
    · intro hb
      exact tiling_preserve_base F ζ hζ U (A.representative i) b (d*b) γ hb
        (by rw [map_mul,hd])
  refine ⟨d,hmul,hpre,?_⟩
  have hm := (measurePreserving_mul_left ν d).restrict_preimage_emb
    ((Homeomorph.mulLeft d).measurableEmbedding) (B F ζ hζ hF U A i)
  rwa [hpre] at hm

open _root_.DedekindZetaZeroFree.KPCompactStabilizerHaarSources renaming cocycle → cocycle
open _root_.DedekindZetaZeroFree.KPCompactStabilizerHaarSources renaming cocycle_continuous → cocycle_continuous

 theorem actual_rational_Iwasawa_fiber
    (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
      (X (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
    (heBase : ∀ a, (e a).1 = KPMsFixedHaarDisintegration.archBasepoint F a)
    (heFiber : ∀ x k j, (e.symm (x,k)) (KPCusp.complexPlace F j) =
      (KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
        (k : G (KPCuspLogShape.dimension F))) j)
    (σ : KPCuspArithmetic.PGL2 F) :
    ∃ κ : X (KPCuspLogShape.dimension F) → K (KPCuspLogShape.dimension F),
      Continuous κ ∧
      (∀ x k, e.symm (σ • x,κ x*k) = rationalArch F ζ hζ σ * e.symm (x,k)) ∧
      ∀ x, MeasurePreserving (fun k => κ x*k)
        (stabilizerHaar (KPCuspLogShape.dimension F))
        (stabilizerHaar (KPCuspLogShape.dimension F)) := by
  let a := archEquiv F ζ hζ
  let d := KPCuspLogShape.dimension F
  let : BorelSpace (K d) := stabilizerBorelSpace d
  have he : ∀ y k, a (e.symm (y,k)) = KPArithmeticAction.productProjectiveSection d y *
      (k : G d) := by
    intro y k
    funext j
    exact heFiber y k j
  have hbase : ∀ y k, KPMsFixedHaarDisintegration.archBasepoint F (e.symm (y,k)) = y := by
    intro y k
    rw [← heBase,e.apply_symm_apply]
  have haction : ∀ x : X d, a (rationalArch F ζ hζ σ) • x = σ • x := by
    intro x
    have hb := rationalArch_equivariant F ζ hζ σ (e.symm (x,1))
    rw [basepoint_eq F ζ hζ,map_mul,mul_smul,← basepoint_eq F ζ hζ] at hb
    change a (rationalArch F ζ hζ σ) •
      KPMsFixedHaarDisintegration.archBasepoint F (e.symm (x,1)) =
      σ • KPMsFixedHaarDisintegration.archBasepoint F (e.symm (x,1)) at hb
    simpa only [hbase] using hb
  refine ⟨cocycle d (a (rationalArch F ζ hζ σ)),cocycle_continuous _ _,?_,?_⟩
  · intro x k
    apply a.injective
    rw [map_mul,he,he]
    change KPArithmeticAction.productProjectiveSection d (σ • x) *
      (((KPArithmeticAction.productProjectiveSection d
        (a (rationalArch F ζ hζ σ) • x))⁻¹ * a (rationalArch F ζ hζ σ) *
          KPArithmeticAction.productProjectiveSection d x) * (k : G d)) = _
    rw [haction]
    simp only [mul_assoc,mul_inv_cancel_left]
  · intro x
    set_option backward.isDefEq.respectTransparency false in
      exact measurePreserving_mul_left _ _

 theorem actual_compact_finite_test_covariance
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : KPMsFixedHaar.Level F ζ hζ)
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (i : Fin A.componentCount)
    (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
      (X (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
    (heBase : ∀ a, (e a).1 = KPMsFixedHaarDisintegration.archBasepoint F a)
    (heFiber : ∀ x k j, (e.symm (x,k)) (KPCusp.complexPlace F j) =
      (KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
        (k : G (KPCuspLogShape.dimension F))) j)
    (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) [ν.IsHaarMeasure]
    [SFinite ν]
    (φ : KPSmoothLocalQuotientCharts.X F ζ hζ → ℝ≥0∞) (hφ : Measurable φ)
    (γ : Gi F ζ hζ hF U A i) (x : X (KPCuspLogShape.dimension F)) :
    (∫⁻ p : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      φ (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (m F ζ hζ (e.symm (γ • x,p.1),p.2)))
      ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod
        (ν.restrict (B F ζ hζ hF U A i))) =
    ∫⁻ p : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      φ (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (m F ζ hζ (e.symm (x,p.1),p.2)))
      ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod
        (ν.restrict (B F ζ hζ hF U A i)) := by
  let d := KPCuspLogShape.dimension F
  let : BorelSpace (K d) := stabilizerBorelSpace d
  let : BorelSpace (KPSmoothActualFlowData.GInfinity F) := ⟨rfl⟩
  let := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  let := ActualQuotient.actual_cover_secondCountable F ζ hζ
  obtain ⟨ep,hep⟩ := actual_product_splitting F ζ hζ
  let : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F ×
      KPFiniteCuspAtlas.FiniteCover F ζ hζ) := ep.toHomeomorph.secondCountableTopology
  let : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F) :=
    (isEmbedding_prodMkLeft (1 : KPFiniteCuspAtlas.FiniteCover F ζ hζ)).secondCountableTopology
  let : SecondCountableTopology (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    (isEmbedding_prodMkRight (1 : KPSmoothActualFlowData.GInfinity F)).secondCountableTopology
  let : BorelSpace (KPSmoothActualFlowData.GInfinity F ×
      KPFiniteCuspAtlas.FiniteCover F ζ hζ) := inferInstance
  obtain ⟨κ,hκ,heTrans,hκMP⟩ := actual_rational_Iwasawa_fiber (ζ := ζ) (hζ := hζ) e heBase heFiber γ.val
  have heTrans' : ∀ k, e.symm (γ • x,κ x*k) = rationalArch F ζ hζ γ.val * e.symm (x,k) :=
    fun k => heTrans x k
  obtain ⟨b,hb,hbB,hbMP⟩ := actual_rational_finite_fiber hF U A i γ ν
  let f : K d × KPFiniteCuspAtlas.FiniteCover F ζ hζ → ℝ≥0∞ := fun p =>
    φ (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (m F ζ hζ (e.symm (γ • x,p.1),p.2)))
  have hfm : Measurable f := by
    apply hφ.comp
    exact (continuous_quotient_mk'.comp
      (((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
        (e.symm.continuous.comp (continuous_const.prodMk continuous_fst))).mul
          (continuous_subtype_val.comp continuous_snd))).measurable
  have hp := (hκMP x).prod hbMP
  have htest : ∀ p : K d × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      f (κ x*p.1,b*p.2) = φ (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (m F ζ hζ (e.symm (x,p.1),p.2))) := by
    intro p
    dsimp only [f]
    rw [heTrans',← hb]
    congr 1
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    have hγ : tilingLift F ζ hζ γ.val ∈ KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ :=
      ⟨rationalEquiv F γ.val,rfl⟩
    simpa only [mul_inv_rev,mul_assoc,mul_inv_cancel_left] using
      (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ).inv_mem hγ
  have hh := hp.lintegral_comp hfm
  change (∫⁻ p : K d × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
    f (κ x*p.1,b*p.2) ∂(stabilizerHaar d).prod (ν.restrict (B F ζ hζ hF U A i))) =
    ∫⁻ p, f p ∂(stabilizerHaar d).prod (ν.restrict (B F ζ hζ hF U A i)) at hh
  simp only [htest] at hh
  exact hh.symm

private theorem actual_component_pinned_domain
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : KPMsFixedHaar.Level F ζ hζ)
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaar.SphericalTransport F ζ hζ)
    (i : Fin A.componentCount) :
    ∃ ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ), ν.IsHaarMeasure ∧
      Measure.map (m F ζ hζ) (R.archHaar.prod ν) = R.adelicHaar ∧
      MeasurableSet (B F ζ hζ hF U A i) ∧
      0 < ν (B F ζ hζ hF U A i) ∧ ν (B F ζ hζ hF U A i) < ⊤ ∧
      R.quotientHaar.restrict (P.projection U ⁻¹' C F ζ hζ hF U A i) =
        Measure.map (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ ∘ m F ζ hζ)
          ((R.archHaar.restrict (KPMsFixedHaarDisintegration.archBasepoint F ⁻¹'
              (A.cuspAtlas i).fundamentalDomain)).prod
            (ν.restrict (B F ζ hζ hF U A i))) := by
  obtain ⟨ν,hν,hproduct,D',hD'm,hD',hBm,hBpositive,hBfinite,hdis⟩ :=
    actual_component_product_disintegration F ζ hζ hF U A R P i
  let := hν
  let := R.arch_isHaar
  let := R.adelic_isHaar
  let D := KPMsFixedHaarDisintegration.archBasepoint F ⁻¹'
    (A.cuspAtlas i).fundamentalDomain
  have hDm : MeasurableSet D :=
    (basepoint_continuous F ζ hζ).measurable (A.cuspAtlas i).measurable_fundamentalDomain
  have hD : IsFundamentalDomain (Ga F ζ hζ hF U A i) D R.archHaar :=
    actual_atlas_group_domain hF U A R i
  obtain ⟨hT,hSm,hSsub,hS⟩ :=
    ProductDisintegration.product_domain_partial_fundamental
      F ζ hζ hF U A R P i ν hproduct D hDm hD
  refine ⟨ν,hν,hproduct,hBm,hBpositive,hBfinite,?_⟩
  let := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  let := ActualQuotient.actual_cover_secondCountable F ζ hζ
  let : Countable (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) := by
    have hΓ := ActualQuotient.actual_rational_closed_discrete F ζ hζ
    exact (IsLindelof.countable_of_isDiscrete hΓ.1.isLindelof hΓ.2).to_subtype
  have hq : Measurable (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) :=
    (show Continuous (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) from
      continuous_quot_mk).measurable
  have hqi : ∀ (γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) y,
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (γ • y) =
        KPSmoothLocalQuotientCharts.quotientMap F ζ hζ y := by
    intro γ y
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simpa [Subgroup.smul_def, mul_assoc] using γ.property
  have hcompare := ProductDisintegration.quotient_restrict_of_partial_domain
    R.adelicHaar R.domain R.domain_measurable R.domain_fundamental
    (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) hq hqi
    (P.projection U ⁻¹' C F ζ hζ hF U A i) hT
    (m F ζ hζ '' (D ×ˢ B F ζ hζ hF U A i)) hSm hSsub hS
  rw [R.quotient_normalization] at hcompare
  rw [hcompare]
  obtain ⟨e, he⟩ := actual_product_splitting F ζ hζ
  let : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F ×
      KPFiniteCuspAtlas.FiniteCover F ζ hζ) := e.toHomeomorph.secondCountableTopology
  let : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F) :=
    (isEmbedding_prodMkLeft (1 : KPFiniteCuspAtlas.FiniteCover F ζ hζ)).secondCountableTopology
  let : SecondCountableTopology (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    (isEmbedding_prodMkRight (1 : KPSmoothActualFlowData.GInfinity F)).secondCountableTopology
  let : BorelSpace (KPSmoothActualFlowData.GInfinity F) := ⟨rfl⟩
  let : BorelSpace (KPSmoothActualFlowData.GInfinity F ×
      KPFiniteCuspAtlas.FiniteCover F ζ hζ) := inferInstance
  let := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  let := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  let : LocallyCompactSpace (KPSmoothActualFlowData.GInfinity F ×
      KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let : LocallyCompactSpace (KPSmoothActualFlowData.GInfinity F) :=
    (isOpenQuotientMap_fst (Y := KPFiniteCuspAtlas.FiniteCover F ζ hζ)).locallyCompactSpace
  let : LocallyCompactSpace (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    (isOpenQuotientMap_snd (X := KPSmoothActualFlowData.GInfinity F)).locallyCompactSpace
  let : SFinite ν := inferInstance
  have hem : MeasurableEmbedding (m F ζ hζ) := by
    have heq : m F ζ hζ = e := by
      funext p
      exact (he p.1 p.2).symm
    rw [heq]
    exact e.toHomeomorph.measurableEmbedding
  have hrestrict : R.adelicHaar.restrict (m F ζ hζ '' (D ×ˢ B F ζ hζ hF U A i)) =
      Measure.map (m F ζ hζ)
        ((R.archHaar.restrict D).prod (ν.restrict (B F ζ hζ hF U A i))) := by
    rw [← hproduct, hem.restrict_map, hem.injective.preimage_image, Measure.prod_restrict]
  rw [hrestrict, Measure.map_map hq hem.measurable]

private theorem actual_component_pinned_full_K
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : KPMsFixedHaar.Level F ζ hζ)
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaar.SphericalTransport F ζ hζ)
    (i : Fin A.componentCount) :
    ∃ (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
      (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
        (X (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F))) (c : ℝ≥0),
      ν.IsHaarMeasure ∧ 0 < c ∧
      (∀ g, (e g).1 = KPMsFixedHaarDisintegration.archBasepoint F g) ∧
      (∀ x k j, (e.symm (x,k)) (KPCusp.complexPlace F j) =
        (KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
          (k : G (KPCuspLogShape.dimension F))) j) ∧
      R.quotientHaar.restrict (P.projection U ⁻¹' C F ζ hζ hF U A i) =
        (c : ℝ≥0∞) • Measure.map
          (fun p : (X (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)) ×
              KPFiniteCuspAtlas.FiniteCover F ζ hζ =>
            KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
              (m F ζ hζ (e.symm p.1,p.2)))
          ((((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict
              (A.cuspAtlas i).fundamentalDomain).prod
              (stabilizerHaar (KPCuspLogShape.dimension F))).prod
            (ν.restrict (B F ζ hζ hF U A i))) := by
  obtain ⟨ν,hν,hproduct,hBm,hBpositive,hBfinite,hdis⟩ :=
    actual_component_pinned_domain hF U A R P i
  obtain ⟨e,c,hc,heBase,heFiber,heMap⟩ := original_recipe_full_K R
  let := hν
  let := R.arch_isHaar
  let := R.adelic_isHaar
  let : BorelSpace (KPSmoothActualFlowData.GInfinity F) := ⟨rfl⟩
  let : BorelSpace (K (KPCuspLogShape.dimension F)) := stabilizerBorelSpace _
  let : IsFiniteMeasureOnCompacts (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) :=
    (hyperbolic_volume_properties (KPCuspLogShape.dimension F)).1
  let M := ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict
    (A.cuspAtlas i).fundamentalDomain).prod (stabilizerHaar (KPCuspLogShape.dimension F))
  let D := KPMsFixedHaarDisintegration.archBasepoint F ⁻¹'
    (A.cuspAtlas i).fundamentalDomain
  have hpre : D = e ⁻¹' ((A.cuspAtlas i).fundamentalDomain ×ˢ Set.univ) := by
    ext g
    simp only [D, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, heBase]
  have hr : Measure.map e (R.archHaar.restrict D) = (c : ℝ≥0∞) • M := by
    rw [hpre, ← Measure.restrict_map e.measurable
      ((A.cuspAtlas i).measurable_fundamentalDomain.prod MeasurableSet.univ), heMap,
      Measure.restrict_smul, ← Measure.restrict_prod_eq_prod_univ]
  have hri : R.archHaar.restrict D = (c : ℝ≥0∞) • Measure.map e.symm M := by
    have ht := congrArg (Measure.map e.symm) hr
    rw [Measure.map_map e.symm.measurable e.measurable,
      Measure.map_smul _ e.symm.measurable.aemeasurable] at ht
    simpa only [Function.comp_def, e.symm_apply_apply, Measure.map_id'] using ht
  have hms : Measurable (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ ∘ m F ζ hζ) := by
    let := ActualQuotient.actual_cover_secondCountable F ζ hζ
    obtain ⟨ep,hep⟩ := actual_product_splitting F ζ hζ
    let : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F ×
        KPFiniteCuspAtlas.FiniteCover F ζ hζ) := ep.toHomeomorph.secondCountableTopology
    let : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F) :=
      (isEmbedding_prodMkLeft (1 : KPFiniteCuspAtlas.FiniteCover F ζ hζ)).secondCountableTopology
    let : SecondCountableTopology (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
      (isEmbedding_prodMkRight (1 : KPSmoothActualFlowData.GInfinity F)).secondCountableTopology
    let : BorelSpace (KPSmoothActualFlowData.GInfinity F ×
        KPFiniteCuspAtlas.FiniteCover F ζ hζ) := inferInstance
    let := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
    exact (continuous_quotient_mk'.comp
      (((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
        continuous_fst).mul (continuous_subtype_val.comp continuous_snd))).measurable
  have hνsf : SFinite ν := by
    obtain ⟨ep,hep⟩ := actual_product_splitting F ζ hζ
    let : SecondCountableTopology (KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ) :=
      ActualQuotient.actual_cover_secondCountable F ζ hζ
    let : LocallyCompactSpace (KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ) :=
      (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
    let : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F ×
        KPFiniteCuspAtlas.FiniteCover F ζ hζ) := ep.toHomeomorph.secondCountableTopology
    let : SecondCountableTopology (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
      (isEmbedding_prodMkRight (1 : KPSmoothActualFlowData.GInfinity F)).secondCountableTopology
    let : LocallyCompactSpace (KPSmoothActualFlowData.GInfinity F ×
        KPFiniteCuspAtlas.FiniteCover F ζ hζ) := ep.toHomeomorph.isClosedEmbedding.locallyCompactSpace
    let : LocallyCompactSpace (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
      (isOpenQuotientMap_snd (X := KPSmoothActualFlowData.GInfinity F)).locallyCompactSpace
    infer_instance
  let := hνsf
  refine ⟨ν,e,c,hν,hc,heBase,heFiber,?_⟩
  rw [hdis, hri, Measure.prod_smul_left,
    Measure.map_smul _ hms.aemeasurable]
  congr 1
  have hp := Measure.map_prod_map M (ν.restrict (B F ζ hζ hF U A i))
    e.symm.measurable measurable_id
  rw [Measure.map_id] at hp
  rw [hp, Measure.map_map hms (e.symm.measurable.prodMap measurable_id)]
  rfl

private theorem actual_component_fiber_projection
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : KPMsFixedHaar.Level F ζ hζ)
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (P : KPMsFixedHaar.SphericalTransport F ζ hζ) (i : Fin A.componentCount)
    (a : KPSmoothActualFlowData.GInfinity F)
    (b : KPFiniteCuspAtlas.FiniteCover F ζ hζ) (hb : b ∈ B F ζ hζ hF U A i) :
    P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (m F ζ hζ (a,b))) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i)
        (KPCuspSiegel.projection F (Gi F ζ hζ hF U A i)
          (KPMsFixedHaarDisintegration.archBasepoint F a)) := by
  obtain ⟨ε,u,rfl⟩ := hb
  simp only [m,P.formula]
  change Quotient.mk _ (KPMsFixedHaarDisintegration.archBasepoint F a,
    KPCuspGenuineMonodromy.central F ζ hζ ε * A.representative i * u) =
    Quotient.mk _ (KPMsFixedHaarDisintegration.archBasepoint F a,A.representative i)
  apply Eq.symm
  apply Quotient.sound
  exact ⟨1,ε,u,by simp,by simp⟩

private theorem actual_component_test_average
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : KPMsFixedHaar.Level F ζ hζ)
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaar.SphericalTransport F ζ hζ)
    (i : Fin A.componentCount) :
    ∃ (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
      (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
        (X (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F))) (c : ℝ≥0),
      ν.IsHaarMeasure ∧ SFinite ν ∧ 0 < c ∧
      (∀ g, (e g).1 = KPMsFixedHaarDisintegration.archBasepoint F g) ∧
      (∀ x k j, (e.symm (x,k)) (KPCusp.complexPlace F j) =
        (KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
          (k : G (KPCuspLogShape.dimension F))) j) ∧
      ∀ (φ : KPSmoothLocalQuotientCharts.X F ζ hζ → ℝ≥0∞), Measurable φ →
      ∃ ψ : KPCuspSiegel.OrbitQuotient F (Gi F ζ hζ hF U A i) → ℝ≥0∞,
        Measurable ψ ∧
        (∀ x, ψ (KPCuspSiegel.projection F (Gi F ζ hζ hF U A i) x) =
          ∫⁻ p : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
            φ (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
              (m F ζ hζ (e.symm (x,p.1),p.2)))
            ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod
              (ν.restrict (B F ζ hζ hF U A i))) ∧
        (∫⁻ y, φ y ∂ R.quotientHaar.restrict (P.projection U ⁻¹' C F ζ hζ hF U A i)) =
          (c : ℝ≥0∞) * ∫⁻ z, ψ z ∂KPFiniteCuspAtlas.quotientVolume F
            (Gi F ζ hζ hF U A i) (A.cuspAtlas i).fundamentalDomain := by
  obtain ⟨ν,e,c,hν,hc,heBase,heFiber,hdis⟩ := actual_component_pinned_full_K hF U A R P i
  let := hν
  let : BorelSpace (K (KPCuspLogShape.dimension F)) := stabilizerBorelSpace _
  let : BorelSpace (KPSmoothActualFlowData.GInfinity F) := ⟨rfl⟩
  let := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  let := ActualQuotient.actual_cover_secondCountable F ζ hζ
  obtain ⟨ep,hep⟩ := actual_product_splitting F ζ hζ
  let : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F ×
      KPFiniteCuspAtlas.FiniteCover F ζ hζ) := ep.toHomeomorph.secondCountableTopology
  let : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F) :=
    (isEmbedding_prodMkLeft (1 : KPFiniteCuspAtlas.FiniteCover F ζ hζ)).secondCountableTopology
  let : SecondCountableTopology (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    (isEmbedding_prodMkRight (1 : KPSmoothActualFlowData.GInfinity F)).secondCountableTopology
  let : BorelSpace (KPSmoothActualFlowData.GInfinity F ×
      KPFiniteCuspAtlas.FiniteCover F ζ hζ) := inferInstance
  have hνsf : SFinite ν := by
    let : LocallyCompactSpace (KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ) :=
      (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
    let : LocallyCompactSpace (KPSmoothActualFlowData.GInfinity F ×
        KPFiniteCuspAtlas.FiniteCover F ζ hζ) := ep.toHomeomorph.isClosedEmbedding.locallyCompactSpace
    let : LocallyCompactSpace (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
      (isOpenQuotientMap_snd (X := KPSmoothActualFlowData.GInfinity F)).locallyCompactSpace
    infer_instance
  let := hνsf
  let : IsFiniteMeasureOnCompacts (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) :=
    (hyperbolic_volume_properties (KPCuspLogShape.dimension F)).1
  refine ⟨ν,e,c,hν,hνsf,hc,heBase,heFiber,?_⟩
  intro φ hφ
  let T := K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ
  let μT := (stabilizerHaar (KPCuspLogShape.dimension F)).prod
    (ν.restrict (B F ζ hζ hF U A i))
  let f : X (KPCuspLogShape.dimension F) × T → ℝ≥0∞ := fun p =>
    φ (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (m F ζ hζ (e.symm (p.1,p.2.1),p.2.2)))
  have hfm : Measurable f := by
    apply hφ.comp
    exact (continuous_quotient_mk'.comp
      (((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
        (e.symm.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))).mul
          (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))).measurable
  let avg : X (KPCuspLogShape.dimension F) → ℝ≥0∞ := fun x => ∫⁻ p, f (x,p) ∂μT
  have hAvg : Measurable avg := hfm.lintegral_prod_right'
  have hAvgInv : ∀ (γ : Gi F ζ hζ hF U A i) x, avg (γ • x) = avg x := by
    intro γ x
    exact actual_compact_finite_test_covariance hF U A i e heBase heFiber ν φ hφ γ x
  let ψ : KPCuspSiegel.OrbitQuotient F (Gi F ζ hζ hF U A i) → ℝ≥0∞ :=
    Quotient.lift avg (by
      intro x y h
      obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
      simpa only [← hγ] using hAvgInv γ y)
  have hψ : Measurable ψ := measurable_from_quotient.mpr hAvg
  refine ⟨ψ,hψ,fun x => rfl,?_⟩
  rw [hdis,lintegral_smul_measure]
  congr 1
  have hq : Measurable (fun p : (X (KPCuspLogShape.dimension F) ×
      K (KPCuspLogShape.dimension F)) × KPFiniteCuspAtlas.FiniteCover F ζ hζ =>
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (m F ζ hζ (e.symm p.1,p.2))) := by
    exact (continuous_quotient_mk'.comp
      (((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
        (e.symm.continuous.comp continuous_fst)).mul
          (continuous_subtype_val.comp continuous_snd))).measurable
  rw [lintegral_map hφ hq]
  let μX := (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict
    (A.cuspAtlas i).fundamentalDomain
  have hAssoc := measurePreserving_prodAssoc μX
    (stabilizerHaar (KPCuspLogShape.dimension F)) (ν.restrict (B F ζ hζ hF U A i))
  have hh := hAssoc.lintegral_comp hfm
  change (∫⁻ p, f (MeasurableEquiv.prodAssoc p)
    ∂(μX.prod (stabilizerHaar (KPCuspLogShape.dimension F))).prod
      (ν.restrict (B F ζ hζ hF U A i))) = _
  rw [hh,lintegral_prod f hfm.aemeasurable]
  rw [KPFiniteCuspAtlas.quotientVolume]
  have hproj : Measurable (KPCuspSiegel.projection F (Gi F ζ hζ hF U A i)) :=
    measurable_quotient_mk''
  rw [lintegral_map hψ hproj]
  rfl

open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming actual_finiteOrbit_positive_finite → actual_finiteOrbit_positive_finite

private theorem actual_component_localized_joint_tests
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : KPMsFixedHaar.Level F ζ hζ)
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaar.SphericalTransport F ζ hζ)
    (i : Fin A.componentCount) :
    ∃ (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
      (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
        (X (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F))) (c : ℝ≥0),
      ν.IsHaarMeasure ∧ SFinite ν ∧ 0 < c ∧
      (∀ g, (e g).1 = KPMsFixedHaarDisintegration.archBasepoint F g) ∧
      (∀ x k j, (e.symm (x,k)) (KPCusp.complexPlace F j) =
        (KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
          (k : G (KPCuspLogShape.dimension F))) j) ∧
      ∀ (φ : KPSmoothLocalQuotientCharts.X F ζ hζ → ℝ≥0∞), Measurable φ →
      ∃ ψ : KPCuspSiegel.OrbitQuotient F (Gi F ζ hζ hF U A i) → ℝ≥0∞,
        Measurable ψ ∧
        (∀ x, ψ (KPCuspSiegel.projection F (Gi F ζ hζ hF U A i) x) =
          ∫⁻ p : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
            φ (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
              (m F ζ hζ (e.symm (x,p.1),p.2)))
            ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod
              (ν.restrict (B F ζ hζ hF U A i))) ∧
        ∀ V : Set (KPMsFixedHaar.Spherical F ζ hζ U), MeasurableSet V →
          (∫⁻ y in P.projection U ⁻¹' V, φ y
            ∂ R.quotientHaar.restrict (P.projection U ⁻¹' C F ζ hζ hF U A i)) =
          (c : ℝ≥0∞) * ∫⁻ z in
            KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) ⁻¹' V,
            ψ z ∂KPFiniteCuspAtlas.quotientVolume F (Gi F ζ hζ hF U A i)
              (A.cuspAtlas i).fundamentalDomain := by
  obtain ⟨ν,e,c,hν,hνsf,hc,heBase,heFiber,havg⟩ := actual_component_test_average hF U A R P i
  let := hν
  let := hνsf
  let : BorelSpace (K (KPCuspLogShape.dimension F)) := stabilizerBorelSpace _
  refine ⟨ν,e,c,hν,hνsf,hc,heBase,heFiber,?_⟩
  intro φ hφ
  obtain ⟨ψ,hψ,hψfun,hψint⟩ := havg φ hφ
  refine ⟨ψ,hψ,hψfun,?_⟩
  intro V hV
  let comp := KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i)
  have hcomp : Measurable comp := by
    have he : comp = A.components ∘ Sigma.mk i := by
      funext x
      exact (A.components_formula i x).symm
    rw [he]
    exact (A.components.continuous.comp continuous_sigmaMk).measurable
  have hVpre := hV.preimage hcomp
  have hVP := hV.preimage (P.continuous U).measurable
  obtain ⟨ψ',hψ',hψ'fun,hψ'int⟩ := havg ((P.projection U ⁻¹' V).indicator φ)
    (hφ.indicator hVP)
  have hBm : MeasurableSet (B F ζ hζ hF U A i) :=
    (actual_finiteOrbit_positive_finite F ζ hζ U (A.representative i) ν).1
  have hbAE : ∀ᵐ p : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ
      ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod (ν.restrict (B F ζ hζ hF U A i)),
      p.2 ∈ B F ζ hζ hF U A i := by
    exact Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hBm)
  have heBase' : ∀ x k, KPMsFixedHaarDisintegration.archBasepoint F (e.symm (x,k)) = x := by
    intro x k
    rw [← heBase,e.apply_symm_apply]
  have hψeq : ψ' = (comp ⁻¹' V).indicator ψ := by
    funext z
    induction z using Quotient.inductionOn with
    | h x =>
      change ψ' (KPCuspSiegel.projection F (Gi F ζ hζ hF U A i) x) =
        (comp ⁻¹' V).indicator ψ (KPCuspSiegel.projection F (Gi F ζ hζ hF U A i) x)
      rw [hψ'fun]
      by_cases hx : comp (KPCuspSiegel.projection F (Gi F ζ hζ hF U A i) x) ∈ V
      · rw [Set.indicator_of_mem (show KPCuspSiegel.projection F (Gi F ζ hζ hF U A i) x ∈ comp ⁻¹' V from hx),hψfun]
        apply lintegral_congr_ae
        filter_upwards [hbAE] with p hp
        have hh := actual_component_fiber_projection hF U A P i (e.symm (x,p.1)) p.2 hp
        rw [heBase'] at hh
        exact Set.indicator_of_mem (by change P.projection U _ ∈ V; rwa [hh]) φ
      · rw [Set.indicator_of_notMem (show KPCuspSiegel.projection F (Gi F ζ hζ hF U A i) x ∉ comp ⁻¹' V from hx)]
        have hh : (∫⁻ p : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
            (P.projection U ⁻¹' V).indicator φ
              (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (m F ζ hζ (e.symm (x,p.1),p.2)))
            ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod
              (ν.restrict (B F ζ hζ hF U A i))) = ∫⁻ p : K (KPCuspLogShape.dimension F) ×
                KPFiniteCuspAtlas.FiniteCover F ζ hζ, 0
                  ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod
                    (ν.restrict (B F ζ hζ hF U A i)) := by
          apply lintegral_congr_ae
          filter_upwards [hbAE] with p hp
          have hh := actual_component_fiber_projection hF U A P i (e.symm (x,p.1)) p.2 hp
          rw [heBase'] at hh
          exact Set.indicator_of_notMem (by change P.projection U _ ∉ V; rwa [hh]) φ
        exact hh.trans lintegral_zero
  rw [← lintegral_indicator hVP]
  rw [hψ'int,hψeq,lintegral_indicator hVpre]

 theorem actual_high_cusp_joint_coarea
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : KPMsFixedHaar.Level F ζ hζ)
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaar.SphericalTransport F ζ hζ)
    (i : Fin A.componentCount) :
    ∃ (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
      (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
        (X (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F))) (c : ℝ≥0),
      ν.IsHaarMeasure ∧ SFinite ν ∧ 0 < c ∧
      (∀ g, (e g).1 = KPMsFixedHaarDisintegration.archBasepoint F g) ∧
      (∀ x k j, (e.symm (x,k)) (KPCusp.complexPlace F j) =
        (KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
          (k : G (KPCuspLogShape.dimension F))) j) ∧
      ∀ (a : Fin (A.cuspAtlas i).cuspCount) (T : ℝ), A.threshold ≤ T →
      ∀ (φ : KPSmoothLocalQuotientCharts.X F ζ hζ → ℝ≥0∞), Measurable φ →
        (∫⁻ y in P.projection U ⁻¹'
          (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) ''
            KPFiniteCuspAtlas.endSet F (Gi F ζ hζ hF U A i)
              ((A.cuspAtlas i).representative a) T), φ y ∂ R.quotientHaar) =
        (c : ℝ≥0∞) * ∫⁻ p : KPCuspCharts.Coordinates F,
          ∫⁻ z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
            φ (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
              (m F ζ hζ (e.symm
                (((A.cuspAtlas i).representative a) • KPCuspCharts.toArch F p,z.1),z.2)))
          ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod
            (ν.restrict (B F ζ hζ hF U A i))
        ∂((((volume.prod ((A.cuspAtlas i).geometry a).shapeMeasure).prod
          (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))).restrict
            {p : KPCuspCharts.Coordinates F | p.1 ∈ ((A.cuspAtlas i).geometry a).fundamentalDomain}).restrict
              {p : KPCuspCharts.Coordinates F | T < p.2}) := by
  obtain ⟨ν,e,c,hν,hνsf,hc,heBase,heFiber,hloc⟩ :=
    actual_component_localized_joint_tests hF U A R P i
  refine ⟨ν,e,c,hν,hνsf,hc,heBase,heFiber,?_⟩
  intro a T hT φ hφ
  obtain ⟨ψ,hψ,hψfun,hψloc⟩ := hloc φ hφ
  let comp := KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i)
  let E := KPFiniteCuspAtlas.endSet F (Gi F ζ hζ hF U A i)
    ((A.cuspAtlas i).representative a) T
  have hcFun : comp = A.components ∘ Sigma.mk i := by
    funext x
    exact (A.components_formula i x).symm
  have hcomp : Continuous comp := by
    rw [hcFun]
    exact A.components.continuous.comp continuous_sigmaMk
  have hcompOpen : IsOpenMap comp := by
    rw [hcFun]
    exact A.components.isOpenMap.comp isOpenMap_sigmaMk
  have hcompInj : Function.Injective comp := by
    rw [hcFun]
    exact A.components.injective.comp (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)
  have hEm : MeasurableSet (comp '' E) :=
    (hcompOpen _ (KPFiniteAdelicCuspEnds.component_open_end F _ _ T)).measurableSet
  have hEsub : P.projection U ⁻¹' (comp '' E) ⊆ P.projection U ⁻¹' C F ζ hζ hF U A i := by
    rintro y ⟨x,hx,he⟩
    exact ⟨x,he⟩
  have heRestrict : (R.quotientHaar.restrict (P.projection U ⁻¹' C F ζ hζ hF U A i)).restrict
      (P.projection U ⁻¹' (comp '' E)) = R.quotientHaar.restrict (P.projection U ⁻¹' (comp '' E)) := by
    rw [Measure.restrict_restrict (hEm.preimage (P.continuous U).measurable),
      Set.inter_eq_left.mpr hEsub]
  have hh := hψloc (comp '' E) hEm
  rw [heRestrict,Set.preimage_image_eq E hcompInj] at hh
  rw [hh]
  congr 1
  have heEnd := KPMsFixedHaar.RadialIntegrationSteps.end_coordinate_lintegral
    A (⟨i,a⟩ : KPMsFixedHaar.CuspIndex A) T hT ψ hψ
  rw [heEnd]
  apply lintegral_congr
  intro p
  exact hψfun _

open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.Step2Proof renaming framedFullAngular_upper_transition → framedFullAngular_upper_transition
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.Step2Proof renaming framedFullAngular → framedFullAngular
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.Step2Proof renaming framedNormOne → framedNormOne
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.Step2Proof renaming framedRadius → framedRadius
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.Step2Proof renaming rational_upper_literal_factorization → rational_upper_literal_factorization

section ActualLift
open KPMsClearedTruncationL2
open KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent
open KPMsResidualTailRestoration.SharpConstantTerm

end ActualLift

open _root_.DedekindZetaZeroFree.KPMsFixedHaarDisintegration renaming toRawTransport → toRawTransport

end DedekindZetaZeroFree.FullAngularHaar.Constructor.JointMeasure

end
