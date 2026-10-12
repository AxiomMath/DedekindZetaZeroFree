module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.BorelOverlapDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentMeasurableMeasure
open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentOverlapRationalBranches
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

def coordHomeomorph : M F ≃ₜ KPCuspGenuineMonodromy.SymmetricSpace F where
  toFun := labeledA (placeEquiv F ζ hζ)
  invFun := labeledAInv (placeEquiv F ζ hζ)
  left_inv x := by simp [labeledAInv, labeledA]
  right_inv x := by funext k; simp [labeledAInv, labeledA]
  continuous_toFun := by
    apply continuous_pi
    intro k
    exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
  continuous_invFun := by
    apply (CotangentLogCoframe.A (d F)).symm.continuous.comp
    exact continuous_pi fun k => continuous_apply _

theorem omega_open (a : ShrunkChart F ζ hζ U R P H) : IsOpen (omega a) :=
  a.domain_open.preimage (coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)).continuous

def chartHomeomorph (a : ShrunkChart F ζ hζ U R P H) : omega a ≃ₜ a.domain :=
  (coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)).subtype (by
    intro x
    rfl)

def chartMeasure (a : ShrunkChart F ζ hζ U R P H) : Measure (omega a) :=
  Measure.comap (Subtype.val : omega a → M F)
    ((KPContCotangentOverlapNullEquivalence.liftedMeasure a).restrict (omega a))

theorem coordinate_lift (a : ShrunkChart F ζ hζ U R P H) :
    chartMeasure a = Measure.map (chartHomeomorph a).symm a.liftedMeasure := by
  let c := coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)
  let e := chartHomeomorph a
  have hv : MeasurableEmbedding (Subtype.val : omega a → M F) :=
    MeasurableEmbedding.subtype_coe (omega_open a).measurableSet
  apply hv.map_injective
  rw [chartMeasure, map_comap_subtype_coe (omega_open a).measurableSet,
    Measure.restrict_restrict_of_subset (subset_refl (omega a))]
  rw [Measure.map_map hv.measurable e.symm.measurable]
  have hcomp : (Subtype.val : omega a → M F) ∘ e.symm =
      fun y : a.domain => labeledAInv (placeEquiv F ζ hζ) y.val := rfl
  rw [hcomp, ← KPContCotangentOverlapNullEquivalence.liftedMeasure]
  apply Measure.restrict_eq_self_of_ae_mem
  have hmem : ∀ᵐ x ∂KPContCotangentOverlapNullEquivalence.liftedMeasure a,
      x ∈ omega a := by
    rw [KPContCotangentOverlapNullEquivalence.liftedMeasure]
    apply ae_map_iff (c.symm.measurable.comp measurable_subtype_coe).aemeasurable
      (omega_open a).measurableSet |>.2
    exact Filter.Eventually.of_forall fun y => by
      change c (c.symm y.val) ∈ a.domain
      simpa using y.property
  exact hmem

theorem q_pushforward (a : ShrunkChart F ζ hζ U R P H) :
    Measurable (fun x : omega a => q a x.val) ∧
    Measure.map (fun x : omega a => q a x.val) (chartMeasure a) =
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict a.baseDomain := by
  have hp := every_shrunkChart_properties F ζ hζ U R P H a
  have hm : (fun x : omega a => q a x.val) = a.toBase ∘ chartHomeomorph a := rfl
  refine ⟨by rw [hm]; exact hp.measurable.comp (chartHomeomorph a).measurable, ?_⟩
  have hq : Measurable (fun x : omega a => q a x.val) := by
    rw [hm]
    exact hp.measurable.comp (chartHomeomorph a).measurable
  rw [coordinate_lift, Measure.map_map hq (chartHomeomorph a).symm.measurable]
  have hc : (fun x : omega a => q a x.val) ∘ (chartHomeomorph a).symm = a.toBase := by
    funext y
    change a.toBase (chartHomeomorph a ((chartHomeomorph a).symm y)) = a.toBase y
    rw [Homeomorph.apply_symm_apply]
  rw [hc, hp.exact_pushforward]

theorem ae_chart_iff (a : ShrunkChart F ζ hζ U R P H)
    (p : KPFiniteCuspAtlas.rawXU F ζ hζ U → Prop) (hp : MeasurableSet {x | p x}) :
    (∀ᵐ x ∂chartMeasure a, p (q a x.val)) ↔
      ∀ᵐ x ∂(KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict a.baseDomain, p x := by
  rw [← (q_pushforward a).2]
  exact (ae_map_iff (q_pushforward a).1.aemeasurable hp).symm

theorem ae_cover_iff (cover : CountableCover F ζ hζ U R P H)
    (p : KPFiniteCuspAtlas.rawXU F ζ hζ U → Prop) (hp : MeasurableSet {x | p x}) :
    (∀ᵐ x ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U, p x) ↔
      ∀ n, ∀ᵐ x ∂chartMeasure (cover.chart n), p (q (cover.chart n) x.val) := by
  simp_rw [ae_chart_iff _ p hp]
  constructor
  · intro h n
    exact ae_restrict_of_ae h
  · intro h
    have hh : ∀ᵐ x ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U,
        ∀ n, x ∈ (cover.chart n).baseDomain → p x := by
      apply ae_all_iff.mpr
      intro n
      exact (ae_restrict_iff' (cover.properties n).base_measurable).mp (h n)
    filter_upwards [hh] with x hx
    have hm : x ∈ ⋃ n, (cover.chart n).baseDomain := by rw [cover.covers]; trivial
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hm
    exact hx n hn

 theorem chart_coord (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)) :
    coordinateMap (isotropyChart a) (targetChart a b h) g =
      fun x => (coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)).symm
        (g.val • coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ) x) := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  funext x
  simp [coordinateMap, isotropyChart, targetChart, ChartKind.representative, coordHomeomorph]

 theorem chart_omega (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component) :
    (targetChart a b h).omega = (isotropyChart b).omega := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  rfl

 theorem omega_subset (a : ShrunkChart F ζ hζ U R P H) :
    omega a ⊆ (isotropyChart a).omega := by
  intro x hx
  exact a.closure_subset (subset_closure hx)

 def rationalBranch (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)) :
    ActualBranch a b := by
  let c := coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)
  let ψ := coordinateMap (isotropyChart a) (targetChart a b h) g
  have hψ : Continuous ψ := by
    dsimp [ψ]
    rw [chart_coord]
    exact c.symm.continuous.comp ((KPCuspSiegel.continuous_action F g.val).comp c.continuous)
  let hex := KPCuspGenuineMonodromy.finiteComparison_exists F ζ hζ U _ g
  let r := hex.choose
  let u := hex.choose_spec.choose
  have hu := hex.choose_spec.choose_spec
  exact {
    component_eq := h
    arrow := {
      gamma := g, root := r⁻¹, levelLift := u
      finite_comparison := by simpa only [inv_inv] using hu
      domain := omega a ∩ ψ ⁻¹' omega b
      isOpen_domain := (omega_open a).inter ((omega_open b).preimage hψ)
      source := fun _ hx => omega_subset a hx.1
      target := by rw [chart_omega a b h]; exact fun _ hx => omega_subset b hx.2 }
    source_shrinking := fun _ hx => hx.1
    target_shrinking := fun _ hx => hx.2
    target_larger := fun _ hx => omega_subset b hx.2 }

private theorem equal_component (a b : ShrunkChart F ζ hζ U R P H)
    (x : omega a) (y : omega b) (h : q a x.val = q b y.val) : a.component = b.component := by
  have hh : (H.atlas U).components
      ⟨a.component, KPCuspSiegel.projection F
        (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)
          (labeledA (placeEquiv F ζ hζ) x.val)⟩ =
    (H.atlas U).components
      ⟨b.component, KPCuspSiegel.projection F
        (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H b.component)
          (labeledA (placeEquiv F ζ hζ) y.val)⟩ := by
    simpa only [(H.atlas U).components_formula, KPContCotangentOverlapRationalBranches.q] using h
  exact congrArg Sigma.fst ((H.atlas U).components.injective hh)

private theorem connecting_branch (a b : ShrunkChart F ζ hζ U R P H)
    (x : omega a) (y : omega b) (h : q a x.val = q b y.val) :
    ∃ e : ActualBranch a b, ∃ hx : x.val ∈ e.arrow.domain, e.arrow.psi x.val = y.val := by
  have hc := equal_component a b x y h
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at hc
  subst j
  have hi : Function.Injective (KPFiniteCuspAtlas.componentMap F ζ hζ U
      ((H.atlas U).representative i)) := by
    intro u v huv
    have he : (H.atlas U).components ⟨i,u⟩ = (H.atlas U).components ⟨i,v⟩ := by
      simpa only [(H.atlas U).components_formula] using huv
    exact eq_of_heq (Sigma.mk.inj ((H.atlas U).components.injective he)).2
  obtain ⟨g,hg⟩ := Quotient.exact (hi h.symm)
  change g • labeledA (placeEquiv F ζ hζ) x.val = labeledA (placeEquiv F ζ hζ) y.val at hg
  let a : ShrunkChart F ζ hζ U R P H := ⟨i,ca,oa,da,dao,dac,das,dai⟩
  let b : ShrunkChart F ζ hζ U R P H := ⟨i,cb,ob,db,dbo,dbc,dbs,dbi⟩
  let e := rationalBranch a b rfl g
  have he : e.arrow.psi x.val = y.val := by
    change coordinateMap (isotropyChart a) (targetChart a b rfl) g x.val = y.val
    rw [chart_coord]
    change (coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)).symm
      (g • labeledA (placeEquiv F ζ hζ) x.val) = y.val
    rw [hg]
    exact (coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)).symm_apply_apply y.val
  refine ⟨e, ?_, he⟩
  change x.val ∈ omega a ∩ e.arrow.psi ⁻¹' omega b
  exact ⟨x.property, by rw [Set.mem_preimage, he]; exact y.property⟩

theorem scalar_fibers {S : Type*}
    (f : ∀ a : ShrunkChart F ζ hζ U R P H, omega a → S)
    (hcompat : ∀ (a b) (e : ActualBranch a b) (x : M F) (hx : x ∈ e.arrow.domain),
      f b ⟨e.arrow.psi x, e.target_shrinking hx⟩ = f a ⟨x,e.source_shrinking hx⟩)
    (a b : ShrunkChart F ζ hζ U R P H) (x : omega a) (y : omega b)
    (h : q a x.val = q b y.val) : f a x = f b y := by
  obtain ⟨e,hx,he⟩ := connecting_branch a b x y h
  have hh := hcompat a b e x.val hx
  have hy : (⟨e.arrow.psi x.val, e.target_shrinking hx⟩ : omega b) = y := Subtype.ext he
  rw [hy] at hh
  exact hh.symm

theorem scalar_descends {S : Type*} [MeasurableSpace S]
    (f : ∀ a : ShrunkChart F ζ hζ U R P H, omega a → S)
    (hf : ∀ a, Measurable (f a))
    (hcompat : ∀ (a b) (e : ActualBranch a b) (x : M F) (hx : x ∈ e.arrow.domain),
      f b ⟨e.arrow.psi x, e.target_shrinking hx⟩ = f a ⟨x,e.source_shrinking hx⟩) :
    ∃! g : KPFiniteCuspAtlas.rawXU F ζ hζ U → S,
      Measurable g ∧ ∀ a (x : omega a), g (q a x.val) = f a x := by
  have local_desc (a : ShrunkChart F ζ hζ U R P H) :
      KPContCotangentFiniteQuotientBorel.BorelDescends a.quotientMap
        (f a ∘ (chartHomeomorph a).symm) := by
    apply KPContCotangentFiniteQuotientBorel.shrunk_chart_borel_descent F ζ hζ U R P H a
      (f a ∘ (chartHomeomorph a).symm) ((hf a).comp (chartHomeomorph a).symm.measurable)
    intro σ y
    apply scalar_fibers f hcompat a a
    have hq (z : a.domain) : q a ((chartHomeomorph a).symm z).val = a.toBase z := by
      change a.toBase (chartHomeomorph a ((chartHomeomorph a).symm z)) = a.toBase z
      rw [Homeomorph.apply_symm_apply]
    rw [hq, hq]
    exact (every_shrunkChart_properties F ζ hζ U R P H a).orbit_fibers _ _ |>.mpr
      ⟨σ⁻¹, by apply Subtype.ext; simp [ShrunkChart.action]⟩
  let g : ∀ a : ShrunkChart F ζ hζ U R P H, a.baseDomain → S :=
    fun a => (local_desc a).choose
  have hg (a) : Measurable (g a) ∧
      ∀ x : omega a, g a ⟨q a x.val, Set.mem_range_self (chartHomeomorph a x)⟩ = f a x := by
    refine ⟨(local_desc a).choose_spec.1.1, ?_⟩
    intro x
    have hh := (local_desc a).choose_spec.1.2 (chartHomeomorph a x)
    change g a ⟨q a x.val, _⟩ = (f a ∘ (chartHomeomorph a).symm) (chartHomeomorph a x) at hh
    simpa only [Function.comp_apply, Homeomorph.symm_apply_apply] using hh
  have gg (a b : ShrunkChart F ζ hζ U R P H) (z : KPFiniteCuspAtlas.rawXU F ζ hζ U)
      (ha : z ∈ a.baseDomain) (hb : z ∈ b.baseDomain) : g a ⟨z,ha⟩ = g b ⟨z,hb⟩ := by
    obtain ⟨x,hx⟩ := ha
    obtain ⟨y,hy⟩ := hb
    have he : q a ((chartHomeomorph a).symm x).val =
        q b ((chartHomeomorph b).symm y).val := by
      change a.toBase (chartHomeomorph a ((chartHomeomorph a).symm x)) =
        b.toBase (chartHomeomorph b ((chartHomeomorph b).symm y))
      simpa only [Homeomorph.apply_symm_apply] using hx.trans hy.symm
    have ha' := (hg a).2 ((chartHomeomorph a).symm x)
    have hb' := (hg b).2 ((chartHomeomorph b).symm y)
    have haz : q a ((chartHomeomorph a).symm x).val = z := by
      change a.toBase (chartHomeomorph a ((chartHomeomorph a).symm x)) = z
      simpa only [Homeomorph.apply_symm_apply] using hx
    have hbz : q b ((chartHomeomorph b).symm y).val = z := by
      change b.toBase (chartHomeomorph b ((chartHomeomorph b).symm y)) = z
      simpa only [Homeomorph.apply_symm_apply] using hy
    have hea : (⟨q a ((chartHomeomorph a).symm x).val,
        Set.mem_range_self (chartHomeomorph a ((chartHomeomorph a).symm x))⟩ : a.baseDomain) =
        ⟨z,⟨x,hx⟩⟩ := Subtype.ext haz
    have heb : (⟨q b ((chartHomeomorph b).symm y).val,
        Set.mem_range_self (chartHomeomorph b ((chartHomeomorph b).symm y))⟩ : b.baseDomain) =
        ⟨z,⟨y,hy⟩⟩ := Subtype.ext hbz
    rw [hea] at ha'
    rw [heb] at hb'
    exact ha'.trans ((scalar_fibers f hcompat a b _ _ he).trans hb'.symm)
  let cover := Classical.choice (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  let G := Set.liftCover (fun n => (cover.chart n).baseDomain)
    (fun n => g (cover.chart n)) (fun n m => gg (cover.chart n) (cover.chart m)) cover.covers
  have hG : Measurable G := measurable_liftCover _
    (fun n => (cover.properties n).base_measurable) _ (fun n => (hg _).1) _ _
  have hGchart (a : ShrunkChart F ζ hζ U R P H) (x : omega a) :
      G (q a x.val) = f a x := by
    have hz : q a x.val ∈ ⋃ n, (cover.chart n).baseDomain := by rw [cover.covers]; trivial
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hz
    dsimp only [G]
    rw [Set.liftCover_of_mem (f := fun n => g (cover.chart n))
      (hf := fun n m => gg (cover.chart n) (cover.chart m)) (hS := cover.covers) hn]
    exact (gg _ a _ hn (Set.mem_range_self (chartHomeomorph a x))).trans ((hg a).2 x)
  refine ⟨G, ⟨hG,hGchart⟩, ?_⟩
  intro G' hG'
  funext z
  have hz : z ∈ ⋃ n, (cover.chart n).baseDomain := by rw [cover.covers]; trivial
  obtain ⟨n,x,hx⟩ := Set.mem_iUnion.mp hz
  have he : q (cover.chart n) ((chartHomeomorph (cover.chart n)).symm x).val = z := by
    change (cover.chart n).toBase
      (chartHomeomorph (cover.chart n) ((chartHomeomorph (cover.chart n)).symm x)) = z
    simpa only [Homeomorph.apply_symm_apply] using hx
  rw [← he, hG'.2, hGchart]

end DedekindZetaZeroFree.KPContActualCotangentMeasurableMeasure

end
