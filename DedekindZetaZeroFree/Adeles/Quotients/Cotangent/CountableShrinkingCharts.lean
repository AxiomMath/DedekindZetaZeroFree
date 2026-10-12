module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.FiniteIsotropyQuotientMeasure
public import DedekindZetaZeroFree.Metaplectic.Cubic.Haar.SphericalSectorRealization

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentCountableShrinking

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContSectorPhaseComponentCharts KPContSectorCoveredQuotientVocabulary
open KPContSectorScalarLineAlgebra KPContSectorSmoothFramesSupport

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

structure ShrunkChart where
  component : Fin (H.atlas U).componentCount
  center : SymmetricSpace F
  larger : OrbifoldChart F ζ hζ U R P H component center
  domain : Set (SymmetricSpace F)
  domain_open : IsOpen domain
  closure_compact : IsCompact (closure domain)
  closure_subset : closure domain ⊆ larger.neighborhood
  invariant : ∀ σ : MulAction.stabilizer (Component F ζ hζ U R P H component) center,
    (fun y : SymmetricSpace F => (σ.val : KPCuspArithmetic.PGL2 F) • y) '' domain = domain

namespace ShrunkChart

variable {F ζ hζ U R P H}
variable (C : ShrunkChart F ζ hζ U R P H)

abbrev Isotropy := MulAction.stabilizer (Component F ζ hζ U R P H C.component) C.center

def intoLarger (y : C.domain) : C.larger.neighborhood :=
  ⟨y.val, C.closure_subset (subset_closure y.property)⟩

def toBase (y : C.domain) : KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative C.component)
    (KPCuspSiegel.projection F (Component F ζ hζ U R P H C.component) y.val)

def baseDomain : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) := Set.range C.toBase

def quotientMap (y : C.domain) : C.baseDomain := ⟨C.toBase y, Set.mem_range_self y⟩

def action (σ : C.Isotropy) (y : C.domain) : C.domain :=
  ⟨(σ.val : KPCuspArithmetic.PGL2 F) • y.val, by
    have h := Set.mem_image_of_mem
      (fun z : SymmetricSpace F => (σ.val : KPCuspArithmetic.PGL2 F) • z) y.property
    exact (congrArg (fun s : Set (SymmetricSpace F) =>
      (σ.val : KPCuspArithmetic.PGL2 F) • y.val ∈ s) (C.invariant σ)).mp h⟩

def lineAction (σ : C.Isotropy) (v : Coefficient F ζ hζ U) : Coefficient F ζ hζ U :=
  phaseTransport F ζ hζ U (((H.atlas U).line C.component).rho σ.val) v

def frame (y : C.domain) : Coefficient F ζ hζ U ≃ₗᵢ[ℂ] Coefficient F ζ hζ U :=
  liftFrame F ζ hζ U y.val

def coefficient (s : Sections F ζ hζ U R P H) (y : C.domain) : Coefficient F ζ hζ U :=
  liftCoefficient F ζ hζ U R P H s C.component y.val

def liftedMeasure : Measure C.domain :=
  ((H.disintegration U).componentWeight C.component /
    (Nat.card C.Isotropy : ℝ≥0∞)) •
      Measure.comap (Subtype.val : C.domain → SymmetricSpace F)
        ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict C.domain)

structure Properties : Prop where
  finite_isotropy : Finite C.Isotropy
  base_open : IsOpen C.baseDomain
  base_measurable : MeasurableSet C.baseDomain
  domain_borel : BorelSpace C.domain
  base_borel : BorelSpace C.baseDomain
  continuous : Continuous C.toBase
  measurable : Measurable C.toBase
  quotient : IsQuotientMap C.quotientMap
  orbit_fibers : ∀ y z : C.domain,
    C.toBase y = C.toBase z ↔ ∃ σ : C.Isotropy, C.action σ y = z
  image_in_larger : C.baseDomain ⊆
    baseChartImage F ζ hζ U R P H C.component C.center C.larger
  normalization_positive : 0 < (H.disintegration U).componentWeight C.component
  normalization_finite : (H.disintegration U).componentWeight C.component < ⊤
  exact_pushforward : Measure.map C.toBase C.liftedMeasure =
    (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict C.baseDomain
  frame_unitary : ∀ (y : C.domain) (v : Coefficient F ζ hζ U), ‖C.frame y v‖ = ‖v‖
  frame_equivariant : ∀ (σ : C.Isotropy) (y : C.domain) (v : Coefficient F ζ hζ U),
    C.frame (C.action σ y) (C.lineAction σ v) = C.lineAction σ (C.frame y v)
  coefficient_equivariant : ∀ (s : Sections F ζ hζ U R P H)
    (σ : C.Isotropy) (y : C.domain),
    C.coefficient s (C.action σ y) = C.lineAction σ (C.coefficient s y)
  scalar_restriction : ∀ (f : GenuineCoveredScalars F ζ hζ U) (y : C.domain),
    (C.coefficient (S F ζ hζ U R P H f) y : ℂ) =
      (J F ζ hζ U f).val (y.val, (H.atlas U).representative C.component)

end ShrunkChart

structure CountableCover where
  chart : ℕ → ShrunkChart F ζ hζ U R P H
  properties : ∀ n, (chart n).Properties
  covers : (⋃ n, (chart n).baseDomain) = Set.univ

structure QuotientRegularity : Prop where
  second_countable : SecondCountableTopology (KPFiniteCuspAtlas.rawXU F ζ hζ U)
  quotient_borel : BorelSpace (KPFiniteCuspAtlas.rawXU F ζ hζ U)
  lifted_second_countable : SecondCountableTopology (SymmetricSpace F)
  lifted_borel : BorelSpace (SymmetricSpace F)

namespace Construction

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem component_open (i : Fin (H.atlas U).componentCount) :
    IsOpenEmbedding (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i)) := by
  have he : KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i) =
      (H.atlas U).components ∘ Sigma.mk i := by
    funext x; exact ((H.atlas U).components_formula i x).symm
  rw [he]
  exact (H.atlas U).components.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk

private theorem projection_open (i : Fin (H.atlas U).componentCount) :
    IsOpenMap (KPCuspSiegel.projection F (Component F ζ hζ U R P H i)) := by
  letI : ContinuousConstSMul (Component F ζ hζ U R P H i) (SymmetricSpace F) :=
    ⟨fun g => KPCuspSiegel.continuous_action F g.val⟩
  exact isOpenMap_quotient_mk'_mul

 theorem base_open (C : ShrunkChart F ζ hζ U R P H) : IsOpen C.baseDomain := by
  have he : C.baseDomain =
      KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative C.component) ''
        (KPCuspSiegel.projection F (Component F ζ hζ U R P H C.component) '' C.domain) := by
    ext z; simp [ShrunkChart.baseDomain, ShrunkChart.toBase]
  rw [he]
  exact (component_open C.component).isOpenMap _ ((projection_open C.component) _ C.domain_open)

private theorem base_continuous (C : ShrunkChart F ζ hζ U R P H) : Continuous C.toBase :=
  (component_open C.component).continuous.comp (continuous_quotient_mk'.comp continuous_subtype_val)

private theorem base_quotient (C : ShrunkChart F ζ hζ U R P H) : IsQuotientMap C.quotientMap := by
  have hopen : IsOpenMap C.toBase :=
    ((component_open C.component).isOpenMap.comp (projection_open C.component)).domRestrict C.domain_open
  exact (hopen.codRestrict (fun x => Set.mem_range_self x)).isQuotientMap
    ((base_continuous C).subtype_mk (fun x => Set.mem_range_self x))
    (fun ⟨x, y, hy⟩ => ⟨y, Subtype.ext hy⟩)

private theorem separated (C : ShrunkChart F ζ hζ U R P H)
    (g : Component F ζ hζ U R P H C.component) (x : SymmetricSpace F)
    (hx : x ∈ C.domain) (hg : g • x ∈ C.domain) : g ∈ C.Isotropy := by
  let g' : ArchComponent F ζ hζ U R P H C.component :=
    ⟨complexProjectiveEmbedding F g.val, Subgroup.mem_map.mpr ⟨g.val,g.property,rfl⟩⟩
  have hh : g' ∈ MulAction.stabilizer _ C.center :=
    C.larger.separated g' ⟨g • x,
      ⟨x,C.closure_subset (subset_closure hx),complexProjectiveEmbedding_smul F g.val x⟩,
      C.closure_subset (subset_closure hg)⟩
  apply MulAction.mem_stabilizer_iff.mpr
  have ht := MulAction.mem_stabilizer_iff.mp hh
  change complexProjectiveEmbedding F g.val • C.center = C.center at ht
  rwa [complexProjectiveEmbedding_smul] at ht

private theorem base_fibers (C : ShrunkChart F ζ hζ U R P H) (y z : C.domain) :
    C.toBase y = C.toBase z ↔ ∃ σ : C.Isotropy, C.action σ y = z := by
  constructor
  · intro he
    have hh := (component_open C.component).injective he
    obtain ⟨g,hg⟩ := Quotient.exact hh
    change g • z.val = y.val at hg
    refine ⟨⟨g⁻¹, separated C g⁻¹ y.val y.property ?_⟩, ?_⟩
    · simpa [← hg] using z.property
    · apply Subtype.ext; change g⁻¹ • y.val = z.val; rw [← hg, inv_smul_smul]
  · rintro ⟨σ,he⟩
    apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative C.component))
    exact Quotient.sound ⟨σ.val⁻¹, by
      change σ.val⁻¹ • z.val = y.val
      have h := congrArg Subtype.val he
      change σ.val • y.val = z.val at h
      rw [← h, inv_smul_smul]⟩

private theorem shrink_exists (i : Fin (H.atlas U).componentCount) (p : SymmetricSpace F) :
    ∃ C : ShrunkChart F ζ hζ U R P H, C.component = i ∧ C.center = p ∧ p ∈ C.domain := by
  let O := Classical.choice (orbifoldChart_exists F ζ hζ U R P H i p)
  letI : Finite (MulAction.stabilizer (Component F ζ hζ U R P H i) p) :=
    chart_stabilizer_finite F ζ hζ U R P H i p O
  letI := Fintype.ofFinite (MulAction.stabilizer (Component F ζ hζ U R P H i) p)
  obtain ⟨W,hWo,hpW,hWsub,hWc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := p)) O.isOpen (Set.singleton_subset_iff.mpr O.center_mem)
  let V := ⋂ g : MulAction.stabilizer (Component F ζ hζ U R P H i) p,
    (fun x : SymmetricSpace F => (g.val : KPCuspArithmetic.PGL2 F) • x) ⁻¹' W
  have hopen : IsOpen V := isOpen_iInter_of_finite fun g =>
    hWo.preimage (KPCuspSiegel.continuous_action F g.val.val)
  have hsub : V ⊆ W := by
    intro x hx
    simpa using Set.mem_iInter.mp hx (1 : MulAction.stabilizer (Component F ζ hζ U R P H i) p)
  have hp : p ∈ V := by
    apply Set.mem_iInter.mpr; intro g
    change g.val • p ∈ W
    rw [MulAction.mem_stabilizer_iff.mp g.property]
    exact hpW (Set.mem_singleton p)
  refine ⟨⟨i,p,O,V,hopen,hWc.of_isClosed_subset isClosed_closure (closure_mono hsub),
    (closure_mono hsub).trans hWsub,?_⟩,rfl,rfl,hp⟩
  intro g
  ext x; constructor
  · rintro ⟨y,hy,rfl⟩
    apply Set.mem_iInter.mpr; intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, ← mul_smul] using Set.mem_iInter.mp hy (h*g)
  · intro hx
    refine ⟨(g.val : KPCuspArithmetic.PGL2 F)⁻¹ • x,?_, smul_inv_smul _ _⟩
    apply Set.mem_iInter.mpr; intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, Subgroup.coe_inv, ← mul_smul]
      using Set.mem_iInter.mp hx (h*g⁻¹)

private theorem exact_measure (C : ShrunkChart F ζ hζ U R P H) :
    Measure.map C.toBase C.liftedMeasure =
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict C.baseDomain := by
  let Γ := Component F ζ hζ U R P H C.component
  let μ := KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)
  let π := KPCuspSiegel.projection F Γ
  let j := KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative C.component)
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := by change Countable (Fin 2 → Fin 2 → F); infer_instance
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Function.Injective.countable Units.val_injective
  letI : Countable (KPCuspArithmetic.PGL2 F) :=
    Function.Surjective.countable Matrix.ProjGenLinGroup.mk_surjective
  letI : Finite C.Isotropy := chart_stabilizer_finite F ζ hζ U R P H C.component C.center C.larger
  letI := Fintype.ofFinite C.Isotropy
  letI : MeasurableConstSMul Γ (SymmetricSpace F) :=
    ⟨fun g => (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F g.val).measurable⟩
  letI : SMulInvariantMeasure Γ (SymmetricSpace F) μ := by
    constructor; intro g s hs
    have hp := KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F g.val
    change (KPArch.hyperbolicVolume _) ((fun z => g.val • z) ⁻¹' s) = _
    rw [← Measure.map_apply hp.measurable hs, hp.map_eq]
  have hp : Measurable π := measurable_quotient_mk''
  letI : OpensMeasurableSpace (KPCuspSiegel.OrbitQuotient F Γ) := ⟨by
    exact MeasurableSpace.generateFrom_le (fun s hs =>
      measurableSet_quotient.mpr ((hs.preimage (show Continuous π from continuous_quotient_mk')).measurableSet))⟩
  have hj : Measurable j := (component_open C.component).continuous.measurable
  open scoped Pointwise in
  have hinv (g : C.Isotropy) : (g.val : Γ) • C.domain = C.domain := C.invariant g
  have hl : Measure.map π ((Fintype.card C.Isotropy : ℝ≥0∞)⁻¹ • μ.restrict C.domain) =
      (KPFiniteCuspAtlas.quotientVolume F Γ ((H.atlas U).cuspAtlas C.component).fundamentalDomain).restrict
        (π '' C.domain) :=
    CoreChartLocalizers.CutoffConstruction.finite_isotropy_quotient_measure
      μ (MulAction.stabilizer Γ C.center) ((H.atlas U).cuspAtlas C.component).fundamentalDomain C.domain
      ((H.atlas U).cuspAtlas C.component).measurable_fundamentalDomain C.domain_open.measurableSet
      ((H.atlas U).cuspAtlas C.component).isFundamentalDomain hinv (separated C)
  have hB : C.baseDomain = j '' (π '' C.domain) := by
    ext z; simp [ShrunkChart.baseDomain, ShrunkChart.toBase, j, π, Γ]
  have hsub : C.baseDomain ⊆ Set.range j := by rw [hB]; exact Set.image_subset_range _ _
  have hpre : j ⁻¹' C.baseDomain = π '' C.domain := by
    rw [hB, Set.preimage_image_eq _ (component_open C.component).injective]
  have hb : C.toBase = j ∘ π ∘ Subtype.val := rfl
  have hμ : Measure.map C.toBase C.liftedMeasure =
      (H.disintegration U).componentWeight C.component •
        Measure.map j (Measure.map π ((Fintype.card C.Isotropy : ℝ≥0∞)⁻¹ • μ.restrict C.domain)) := by
    unfold ShrunkChart.liftedMeasure
    rw [Nat.card_eq_fintype_card, div_eq_mul_inv, mul_smul,
      Measure.map_smul _ (base_continuous C).measurable.aemeasurable]
    congr 1
    rw [Measure.map_smul _ (base_continuous C).measurable.aemeasurable, hb, ← Function.comp_assoc,
      ← Measure.map_map (hj.comp hp) measurable_subtype_coe,
      map_comap_subtype_coe C.domain_open.measurableSet,
      Measure.restrict_restrict_of_subset Set.Subset.rfl,
      ← Measure.map_map hj hp, Measure.map_smul _ hp.aemeasurable,
      Measure.map_smul _ hj.aemeasurable]
  rw [hμ, hl, ← hpre, ← Measure.restrict_map hj (base_open C).measurableSet,
    ← Measure.restrict_smul]
  have hm := congrArg (fun ν : Measure (KPFiniteCuspAtlas.rawXU F ζ hζ U) => ν.restrict C.baseDomain)
    ((H.disintegration U).component_measure C.component)
  rw [Measure.restrict_restrict_of_subset hsub] at hm
  exact hm.symm

private theorem all_properties (C : ShrunkChart F ζ hζ U R P H) : C.Properties := by
  refine ⟨chart_stabilizer_finite F ζ hζ U R P H C.component C.center C.larger,
    base_open C, (base_open C).measurableSet, inferInstance, inferInstance,
    base_continuous C, (base_continuous C).measurable, base_quotient C, base_fibers C, ?_,
    (H.disintegration U).positive_componentWeight C.component,
    (H.disintegration U).finite_componentWeight C.component, exact_measure C, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨y,rfl⟩
    refine ⟨KPCuspSiegel.projection F (Component F ζ hζ U R P H C.component) y.val,
      ⟨y.val, C.closure_subset (subset_closure y.property),rfl⟩, ?_⟩
    exact (H.atlas U).components_formula C.component _
  · intro y v; exact liftFrame_unitary F ζ hζ U y.val v
  · intro σ y v
    exact liftFrame_equivariant F ζ hζ U R P H C.component σ.val y.val v
  · intro s σ y
    exact (liftCoefficient_transition F ζ hζ U R P H s C.component σ.val y.val).1
  · intro f y
    exact congrFun (lift_restriction_commutes F ζ hζ U R P H f C.component C.domain) y

private theorem regularity : QuotientRegularity F ζ hζ U := by
  exact ⟨inferInstance,inferInstance,inferInstance,inferInstance⟩

private theorem cover_exists : Nonempty (CountableCover F ζ hζ U R P H) := by
  have hcover : ∀ x : KPFiniteCuspAtlas.rawXU F ζ hζ U,
      ∃ C : ShrunkChart F ζ hζ U R P H, x ∈ C.baseDomain := by
    intro x
    obtain ⟨⟨i,q⟩,rfl⟩ := (H.atlas U).components.surjective x
    obtain ⟨p,rfl⟩ := Quotient.mk_surjective q
    obtain ⟨C,hi,hp,hmem⟩ := shrink_exists (H := H) i p
    refine ⟨C, ⟨⟨p,hmem⟩,?_⟩⟩
    change KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative C.component)
      (KPCuspSiegel.projection F (Component F ζ hζ U R P H C.component) p) = _
    rw [hi]
    exact ((H.atlas U).components_formula i _).symm
  choose chart hchart using hcover
  letI : Nonempty (KPFiniteCuspAtlas.rawXU F ζ hζ U) := ⟨Quotient.mk _ (0,1)⟩
  letI : SecondCountableTopology (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
    (regularity (F := F) (ζ := ζ) (hζ := hζ) (U := U)).second_countable
  letI : HereditarilyLindelofSpace (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
    SecondCountableTopology.toHereditarilyLindelof
  letI : LindelofSpace (KPFiniteCuspAtlas.rawXU F ζ hζ U) := HereditarilyLindelof.to_Lindelof
  obtain ⟨s,hsc,hscov⟩ := isLindelof_univ.elim_countable_subcover
    (fun x => (chart x).baseDomain) (fun x => base_open (chart x)) (by
      intro x hx; exact Set.mem_iUnion.mpr ⟨x,hchart x⟩)
  let x₀ : KPFiniteCuspAtlas.rawXU F ζ hζ U := Quotient.mk _ (0,1)
  obtain ⟨seq,hseq⟩ := (Set.countable_iff_exists_subset_range).mp hsc
  refine ⟨⟨fun n => chart (seq n), fun n => all_properties _, ?_⟩⟩
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hscov (Set.mem_univ x))
  obtain ⟨n,hn⟩ := hseq hy
  exact Set.mem_iUnion.mpr ⟨n, hn ▸ hxy⟩

end Construction

theorem every_shrunkChart_properties (C : ShrunkChart F ζ hζ U R P H) : C.Properties :=
  Construction.all_properties C

theorem quotientRegularity :
    QuotientRegularity F ζ hζ U :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end DedekindZetaZeroFree.KPContActualCotangentCountableShrinking

namespace DedekindZetaZeroFree

theorem kp_cont_actual_cotangent_countable_shrinking
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :
    KPContActualCotangentCountableShrinking.QuotientRegularity F ζ hζ U ∧
      Nonempty (KPContActualCotangentCountableShrinking.CountableCover F ζ hζ U R P H) := by
  exact ⟨KPContActualCotangentCountableShrinking.quotientRegularity F ζ hζ U,
    KPContActualCotangentCountableShrinking.Construction.cover_exists⟩

end DedekindZetaZeroFree

end
