module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.HausdorffTopology

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.CoreChartLocalizers.CutoffConstruction

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

structure FiniteSmoothChartPartition (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (K : Set (X F ζ hζ U)) where
  count : ℕ
  empty_case : K = ∅ → count = 0
  chart : Fin count → Chart F ζ hζ hF U A
  chart_open : ∀ i, IsOpen ((chart i).O F ζ hζ hF U)
  phi : Fin count → X F ζ hζ U → ℝ
  nonnegative_phi : ∀ i x, 0 ≤ phi i x
  compact_phi : ∀ i, HasCompactSupport (phi i)
  support_phi : ∀ i, tsupport (phi i) ⊆ (chart i).O F ζ hζ hF U
  smooth_phi : ∀ i j, ContDiff ℝ (⊤ : ℕ∞)
    (fun z => phi i (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j)
      (KPCuspSiegel.projection F _ z)))
  neighborhood : Set (X F ζ hζ U)
  open_neighborhood : IsOpen neighborhood
  covers_compact : K ⊆ neighborhood
  partition : ∀ x ∈ neighborhood, ∑ i, phi i x = 1

set_option maxHeartbeats 800000 in

theorem chart_base_fibers (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : Chart F ζ hζ hF U A) {x y : E C.n}
    (hx : x ∈ C.extendedDomain) (hy : y ∈ C.extendedDomain) :
    C.toBase F ζ hζ hF U x = C.toBase F ζ hζ hF U y ↔
      ∃ g : C.G F ζ hζ hF U, C.orthogonal g x = y := by
  constructor
  · intro h
    have hb : KPCuspSiegel.projection F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component))
          (C.coordinates x) =
        KPCuspSiegel.projection F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component))
          (C.coordinates y) := by
      have he := A.components.injective
        ((A.components_formula C.component _).trans
          (h.trans (A.components_formula C.component _).symm))
      exact eq_of_heq (Sigma.mk.inj he).2
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact hb))
    have hγ' : ((γ⁻¹ : KPCuspGenuineMonodromy.Component F ζ hζ U
        (A.representative C.component)) : KPCuspArithmetic.PGL2 F) •
        C.coordinates x = C.coordinates y := by
      change γ⁻¹ • C.coordinates x = C.coordinates y
      rw [← hγ]
      simp
    let g : C.G F ζ hζ hF U := ⟨γ⁻¹, C.separated γ⁻¹ x y hx hy hγ'⟩
    have hgx : C.orthogonal g x ∈ C.extendedDomain := by
      rw [← C.invariant_extension g]
      exact ⟨x, hx, rfl⟩
    refine ⟨g, ?_⟩
    apply congrArg Subtype.val
      (C.coordinates_embedding.injective (a₁ := ⟨C.orthogonal g x, hgx⟩)
        (a₂ := ⟨y, hy⟩) ?_)
    change C.coordinates (C.orthogonal g x) = C.coordinates y
    exact (C.equivariance g x hx).trans hγ'
  · rintro ⟨g, rfl⟩
    unfold Chart.toBase
    rw [C.equivariance g x hx]
    apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component))
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    exact MulAction.mem_orbit_iff.mpr ⟨g.val⁻¹, by
      change g.val⁻¹ • (g.val • C.coordinates x) = C.coordinates x
      simp⟩

set_option maxHeartbeats 800000 in

theorem chart_base_fiber_norm (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : Chart F ζ hζ hF U A) {x y : E C.n}
    (hx : x ∈ C.extendedDomain) (hy : y ∈ C.extendedDomain)
    (h : C.toBase F ζ hζ hF U x = C.toBase F ζ hζ hF U y) :
    ‖x‖ = ‖y‖ := by
  obtain ⟨g, rfl⟩ := (chart_base_fibers F ζ hζ hF U A C hx hy).mp h
  exact (C.orthogonal g).norm_map x |>.symm

set_option maxHeartbeats 800000 in

theorem chart_invariant_coordinate_bump (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : Chart F ζ hζ hF U A) {x : E C.n} (hx : x ∈ Metric.ball 0 C.radius) :
    ∃ b : E C.n → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
      tsupport b ⊆ Metric.ball 0 C.radius ∧
      (∀ y, 0 ≤ b y) ∧ 0 < b x ∧
      ∀ (g : C.G F ζ hζ hF U) y, b (C.orthogonal g y) = b y := by
  obtain ⟨f, hs, hc, hd, hb, hfx⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (Metric.isOpen_ball.mem_nhds hx)
  let b : E C.n → ℝ := fun y => ∑ g : C.G F ζ hζ hF U, f (C.orthogonal g y)
  have hb0 : ∀ y, 0 ≤ b y := by
    intro y
    exact Finset.sum_nonneg (fun g _ => (hb ⟨C.orthogonal g y, rfl⟩).1)
  have hbs : tsupport b ⊆ Metric.ball 0 C.radius := by
    have hfc : ∀ g : C.G F ζ hζ hF U,
        tsupport (fun y => f (C.orthogonal g y)) ⊆ Metric.ball 0 C.radius := by
      intro g y hy
      have ht : C.orthogonal g y ∈ tsupport f := by
        have hcont : Continuous (fun y : E C.n => C.orthogonal g y) :=
          (C.orthogonal g).continuous
        exact (hcont.closure_preimage_subset (Function.support f)) hy
      have hh := hs ht
      simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hh
    have hsub : tsupport b ⊆ ⋃ g : C.G F ζ hζ hF U,
        tsupport (fun y => f (C.orthogonal g y)) := by
      apply closure_minimal
      · intro y hy
        by_contra hn
        have hz : ∀ g : C.G F ζ hζ hF U, f (C.orthogonal g y) = 0 := by
          intro g
          by_contra hnz
          exact hn (Set.mem_iUnion.mpr ⟨g, subset_tsupport _ hnz⟩)
        exact hy (by simp [b, hz])
      · exact isClosed_iUnion_of_finite (fun _ => isClosed_tsupport _)
    exact hsub.trans (Set.iUnion_subset hfc)
  refine ⟨b, ?_, ?_, hbs, hb0, ?_, ?_⟩
  · exact ContDiff.sum (fun g _ => hd.comp (C.orthogonal g).contDiff)
  · have hh : ∀ g : C.G F ζ hζ hF U,
        HasCompactSupport (fun y => f (C.orthogonal g y)) := by
      intro g
      exact hc.comp_homeomorph (C.orthogonal g).toHomeomorph
    convert (HasCompactSupport.finset_sum (s := Finset.univ) (fun g _ => hh g)) using 1
    ext y
    exact (Finset.sum_apply y Finset.univ (fun g y => f (C.orthogonal g y))).symm
  · have hle : f (C.orthogonal 1 x) ≤ b x :=
      Finset.single_le_sum (fun g _ => (hb ⟨C.orthogonal g x, rfl⟩).1) (Finset.mem_univ 1)
    have h1 : f (C.orthogonal 1 x) = 1 := by simpa using hfx
    linarith
  · intro g y
    apply Fintype.sum_bijective (fun h : C.G F ζ hζ hF U => h * g)
      (Group.mulRight_bijective g)
    intro h
    rw [map_mul]
    rfl

set_option maxHeartbeats 800000 in

theorem chart_ball_toBase_isOpenMap (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : Chart F ζ hζ hF U A) :
    IsOpenMap (Set.restrict (Metric.ball (0 : E C.n) C.radius)
      (C.toBase F ζ hζ hF U)) := by
  have he : IsOpenEmbedding (Set.restrict C.extendedDomain C.coordinates) := by
    refine ⟨C.coordinates_embedding, ?_⟩
    convert C.coordinates_open using 1
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hb : Metric.ball (0 : E C.n) C.radius ⊆ C.extendedDomain :=
    fun _ hx => C.closed_ball_in_extension (subset_closure hx)
  have hcoord : IsOpenMap
      (Set.restrict (Metric.ball (0 : E C.n) C.radius) C.coordinates) := by
    have hh := he.isOpenMap.comp (Metric.isOpen_ball.isOpenMap_inclusion hb)
    exact hh
  have hmap := A.components.isOpenMap.comp
    ((isOpenMap_sigmaMk (i := C.component)).comp
      ((KPCuspSiegel.isOpenMap_projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component))).comp hcoord))
  convert hmap using 1
  funext y
  change KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component)
    (KPCuspSiegel.projection F _ (C.coordinates y.val)) =
    A.components ⟨C.component, KPCuspSiegel.projection F _ (C.coordinates y.val)⟩
  exact (A.components_formula C.component (KPCuspSiegel.projection F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component))
      (C.coordinates y.val))).symm

private theorem chart_toBase_continuousOn (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : Chart F ζ hζ hF U A) :
    ContinuousOn (C.toBase F ζ hζ hF U) C.extendedDomain := by
  have h : Continuous (fun z : KPFiniteCuspAtlas.SymmetricSpace F =>
      A.components ⟨C.component, KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component)) z⟩) :=
    A.components.continuous.comp (continuous_sigmaMk.comp continuous_quot_mk)
  convert h.comp_continuousOn C.smooth_coordinates.continuousOn using 1
  funext z
  exact (A.components_formula C.component _).symm

set_option maxHeartbeats 800000 in

theorem chart_descend_coordinate_bump (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : Chart F ζ hζ hF U A) (b : E C.n → ℝ)
    (hb : Continuous b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Metric.ball 0 C.radius)
    (hn : ∀ y, 0 ≤ b y)
    (hi : ∀ (g : C.G F ζ hζ hF U) y, b (C.orthogonal g y) = b y) :
    ∃ f : X F ζ hζ U → ℝ,
      Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ C.O F ζ hζ hF U ∧
      (∀ x, 0 ≤ f x) ∧
      ∀ y ∈ C.extendedDomain, f (C.toBase F ζ hζ hF U y) = b y := by
  letI := quotient_hausdorff F ζ hζ hF U A
  let p := C.toBase F ζ hζ hF U
  let B := Metric.ball (0 : E C.n) C.radius
  have hBe : B ⊆ C.extendedDomain := fun _ hy =>
    C.closed_ball_in_extension (subset_closure hy)
  have hp := chart_toBase_continuousOn F ζ hζ hF U A C
  let lift : C.O F ζ hζ hF U → E C.n := fun x => x.property.choose
  have hl : ∀ x : C.O F ζ hζ hF U, lift x ∈ B ∧ p (lift x) = x :=
    fun x => x.property.choose_spec
  let f : X F ζ hζ U → ℝ := fun x =>
    if hx : x ∈ C.O F ζ hζ hF U then b (lift ⟨x, hx⟩) else 0
  have hformula : ∀ y ∈ B, f (p y) = b y := by
    intro y hy
    have hpy : p y ∈ C.O F ζ hζ hF U := ⟨y, hy, rfl⟩
    rw [show f (p y) = b (lift ⟨p y, hpy⟩) by simp [f, hpy]]
    obtain ⟨g, hg⟩ := (chart_base_fibers F ζ hζ hF U A C
      (hBe (hl ⟨p y, hpy⟩).1) (hBe hy)).mp (hl ⟨p y, hpy⟩).2
    exact (hi g _).symm.trans (congrArg b hg)
  have himage : IsCompact (p '' tsupport b) :=
    hc.image_of_continuousOn (hp.mono (hs.trans hBe))
  have hsupport : Function.support f ⊆ p '' tsupport b := by
    intro x hx
    by_cases hxO : x ∈ C.O F ζ hζ hF U
    · refine ⟨lift ⟨x, hxO⟩, ?_, (hl ⟨x, hxO⟩).2⟩
      apply subset_tsupport
      simpa [f, hxO] using hx
    · exact False.elim (hx (by simp [f, hxO]))
  have hts : tsupport f ⊆ p '' tsupport b :=
    closure_minimal hsupport himage.isClosed
  have hcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hxO : x ∈ C.O F ζ hζ hF U
    · let y : B := ⟨lift ⟨x, hxO⟩, (hl ⟨x, hxO⟩).1⟩
      have hpB : Continuous (Set.restrict B p) :=
        continuousOn_iff_continuous_restrict.mp (hp.mono hBe)
      have hmap := (chart_ball_toBase_isOpenMap F ζ hζ hF U A C).map_nhds_eq
        (hpB.continuousAt (x := y))
      have hh : ContinuousAt (f ∘ Set.restrict B p) y := by
        have heq : f ∘ Set.restrict B p = b ∘ Subtype.val := by
          funext z
          exact hformula z z.property
        rw [heq]
        exact (hb.comp continuous_subtype_val).continuousAt
      change Filter.Tendsto f (nhds x) (nhds (f x))
      have hyx : Set.restrict B p y = x := (hl ⟨x, hxO⟩).2
      rw [hyx] at hmap
      rw [← hmap]
      simpa only [ContinuousAt, Filter.tendsto_map'_iff, Function.comp_apply, hyx] using hh
    · have hxS : x ∉ p '' tsupport b := by
        rintro ⟨y, hy, rfl⟩
        exact hxO ⟨y, hs hy, rfl⟩
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [himage.isClosed.isOpen_compl.mem_nhds hxS] with z hz
      exact (notMem_tsupport_iff_eventuallyEq.mp (fun ht => hz (hts ht))).self_of_nhds
  refine ⟨f, hcont, himage.of_isClosed_subset (isClosed_tsupport f) hts,
    hts.trans (Set.image_mono hs), ?_, ?_⟩
  · intro x
    dsimp [f]
    split_ifs
    · exact hn _
    · exact le_rfl
  · intro y hy
    by_cases hyB : y ∈ B
    · exact hformula y hyB
    · have hpy : p y ∉ C.O F ζ hζ hF U := by
        rintro ⟨z, hz, heq⟩
        have hnorm := chart_base_fiber_norm F ζ hζ hF U A C hy (hBe hz) heq.symm
        apply hyB
        simpa only [B, Metric.mem_ball, dist_zero_right, hnorm] using hz
      have hyb : b y = 0 := by
        by_contra hne
        exact hyB (hs (subset_tsupport b hne))
      change f (p y) = b y
      simp only [f, dif_neg hpy, hyb]

private theorem chart_action_smooth (γ : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : KPFiniteCuspAtlas.SymmetricSpace F => γ • z) := by
  change ContDiff ℝ (⊤ : ℕ∞) (KPCuspSiegel.action F γ)
  unfold KPCuspSiegel.action KPCuspSiegel.glAction
  exact (KPArch.productAction_contDiff _ _).of_le (by simp)

private theorem component_projection_invariant (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (j : Fin A.componentCount)
    (γ : KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j))
    (z : KPFiniteCuspAtlas.SymmetricSpace F) :
    KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j)
      (KPCuspSiegel.projection F _ (γ • z)) =
    KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j)
      (KPCuspSiegel.projection F _ z) := by
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j))
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  exact MulAction.mem_orbit_iff.mpr ⟨γ, rfl⟩

set_option maxHeartbeats 800000 in

theorem chart_descended_bump_smooth (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : Chart F ζ hζ hF U A) (b : E C.n → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (f : X F ζ hζ U → ℝ)
    (hf : tsupport f ⊆ C.O F ζ hζ hF U)
    (hformula : ∀ y ∈ C.extendedDomain, f (C.toBase F ζ hζ hF U y) = b y)
    (j : Fin A.componentCount) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z =>
      f (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j)
        (KPCuspSiegel.projection F _ z))) := by
  let q : KPFiniteCuspAtlas.SymmetricSpace F → X F ζ hζ U := fun z =>
    KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j)
      (KPCuspSiegel.projection F _ z)
  have hq : Continuous q := by
    convert A.components.continuous.comp (continuous_sigmaMk.comp
      (show Continuous (KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j))) from
          continuous_quot_mk)) using 1
    funext z
    exact (A.components_formula j _).symm
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : q z ∈ tsupport f
  · obtain ⟨y, hy, he⟩ := hf hz
    have heq := A.components.injective
      ((A.components_formula C.component _).trans
        (he.trans (A.components_formula j _).symm))
    have hj : C.component = j := (Sigma.mk.inj heq).1
    subst j
    have he' : KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component))
        (C.coordinates y) = KPCuspSiegel.projection F _ z :=
      eq_of_heq (Sigma.mk.inj heq).2
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact he'))
    obtain ⟨inv, hinv, hleft⟩ := C.smooth_inverse
    let act : KPFiniteCuspAtlas.SymmetricSpace F → KPFiniteCuspAtlas.SymmetricSpace F :=
      fun w => (γ : KPCuspArithmetic.PGL2 F) • w
    have ha : ContDiff ℝ (⊤ : ℕ∞) act := chart_action_smooth F _
    have haz : act z ∈ C.coordinates '' C.extendedDomain := by
      refine ⟨y, C.closed_ball_in_extension (subset_closure hy), ?_⟩
      exact hγ.symm
    have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => b (inv (act w))) z :=
      hb.contDiffAt.comp z
        ((hinv.contDiffAt (C.coordinates_open.mem_nhds haz)).comp z ha.contDiffAt)
    apply hs.congr_of_eventuallyEq
    filter_upwards [ha.continuous.continuousAt.preimage_mem_nhds
      (C.coordinates_open.mem_nhds haz)] with w hw
    obtain ⟨v, hv, hev⟩ := hw
    have hh : inv (act w) = v := hev ▸ hleft v hv
    change f (q w) = b (inv (act w))
    rw [hh, ← hformula v hv]
    change f (q w) = f (q (C.coordinates v))
    rw [hev]
    exact congrArg f (component_projection_invariant F ζ hζ hF U A C.component γ w).symm
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hq.continuousAt.preimage_mem_nhds
      ((isClosed_tsupport f).isOpen_compl.mem_nhds hz)] with w hw
    exact image_eq_zero_of_notMem_tsupport hw

set_option maxHeartbeats 800000 in

theorem chart_scalar_bump (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : Chart F ζ hζ hF U A) {x : X F ζ hζ U}
    (hx : x ∈ C.O F ζ hζ hF U) :
    ∃ f : X F ζ hζ U → ℝ,
      Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ C.O F ζ hζ hF U ∧
      (∀ y, 0 ≤ f y) ∧ 0 < f x ∧
      ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun z =>
        f (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j)
          (KPCuspSiegel.projection F _ z))) := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨b, hb, hc, hs, hn, hpos, hi⟩ :=
    chart_invariant_coordinate_bump F ζ hζ hF U A C hy
  obtain ⟨f, hfc, hfcomp, hfsub, hfn, hform⟩ :=
    chart_descend_coordinate_bump F ζ hζ hF U A C b hb.continuous hc hs hn hi
  refine ⟨f, hfc, hfcomp, hfsub, hfn, ?_, ?_⟩
  · rw [hform y (C.closed_ball_in_extension (subset_closure hy))]
    exact hpos
  · exact chart_descended_bump_smooth F ζ hζ hF U A C b hb f hfsub hform

theorem finite_smooth_chart_partition (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (hcharts : ∀ x : X F ζ hζ U, ∃ C : Chart F ζ hζ hF U A,
      IsOpen (C.O F ζ hζ hF U) ∧ x ∈ C.O F ζ hζ hF U)
    (K : Set (X F ζ hζ U)) (hK : IsCompact K) :
    Nonempty (FiniteSmoothChartPartition F ζ hζ hF U A K) := by
  classical
  by_cases hKe : K = ∅
  · refine ⟨{ count := 0
              empty_case := fun _ => rfl
              chart := Fin.elim0
              chart_open := fun i => Fin.elim0 i
              phi := Fin.elim0
              nonnegative_phi := fun i => Fin.elim0 i
              compact_phi := fun i => Fin.elim0 i
              support_phi := fun i => Fin.elim0 i
              smooth_phi := fun i => Fin.elim0 i
              neighborhood := ∅
              open_neighborhood := isOpen_empty
              covers_compact := by simp [hKe]
              partition := by simp }⟩
  choose C hCo hxC using hcharts
  choose b hb hc hs hn hpos hsm using
    fun x => chart_scalar_bump F ζ hζ hF U A (C x) (hxC x)
  obtain ⟨s, hcover⟩ := hK.elim_finite_subcover (fun x => {y | 0 < b x y})
    (fun x => isOpen_lt continuous_const (hb x)) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨x, hpos x⟩)
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let bs : Fin (Fintype.card s) → X F ζ hζ U → ℝ := fun i => b (e i)
  let S : X F ζ hζ U → ℝ := fun x => ∑ i, bs i x
  have hS : Continuous S := continuous_finset_sum _ (fun i _ => hb (e i))
  have hS0 : ∀ x, 0 ≤ S x := fun x => Finset.sum_nonneg (fun i _ => hn (e i) x)
  have hSK : ∀ x ∈ K, 0 < S x := by
    intro x hx
    obtain ⟨y, hys⟩ := Set.mem_iUnion.mp (hcover hx)
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.mp hys
    have he : (e (e.symm ⟨y, hy⟩) : X F ζ hζ U) = y := by simp
    have hle : bs (e.symm ⟨y, hy⟩) x ≤ S x :=
      Finset.single_le_sum (fun i _ => hn (e i) x) (Finset.mem_univ _)
    exact (show 0 < bs (e.symm ⟨y, hy⟩) x by simpa [bs, he] using hxy).trans_le hle
  obtain ⟨a, ha, haK⟩ := hK.exists_forall_le' hS.continuousOn hSK
  let δ := a / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let D : ℝ → ℝ := fun t => t + δ * Real.smoothTransition (2 - 2 * t / δ)
  have hD : ContDiff ℝ (⊤ : ℕ∞) D :=
    contDiff_id.add (contDiff_const.mul (Real.smoothTransition.contDiff.comp
      (contDiff_const.sub ((contDiff_const.mul contDiff_id).div_const δ))))
  have hDpos : ∀ t, 0 ≤ t → 0 < D t := by
    intro t ht
    by_cases h : 0 < t
    · exact add_pos_of_pos_of_nonneg h
        (mul_nonneg hδ.le (Real.smoothTransition.nonneg _))
    · have ht0 : t = 0 := le_antisymm (not_lt.mp h) ht
      simp only [D, ht0, mul_zero, zero_div, sub_zero, zero_add,
        Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2), mul_one]
      exact hδ
  have hDeq : ∀ t, δ ≤ t → D t = t := by
    intro t ht
    have hd : 2 - 2 * t / δ ≤ 0 := by
      have hh := (le_div_iff₀ hδ).mpr (by nlinarith : 2 * δ ≤ 2 * t)
      linarith
    simp [D, Real.smoothTransition.zero_of_nonpos hd]
  let phi : Fin (Fintype.card s) → X F ζ hζ U → ℝ :=
    fun i x => bs i x / D (S x)
  have hts : ∀ i, tsupport (phi i) ⊆ tsupport (bs i) := by
    intro i
    apply closure_mono
    intro x hx
    exact fun hh => hx (by simp [phi, hh])
  refine ⟨{ count := Fintype.card s
            empty_case := fun hk => False.elim (hKe hk)
            chart := fun i => C (e i)
            chart_open := fun i => hCo (e i)
            phi := phi
            nonnegative_phi := fun i x => div_nonneg (hn (e i) x) (hDpos _ (hS0 x)).le
            compact_phi := fun i => (hc (e i)).of_isClosed_subset
              (isClosed_tsupport _) (hts i)
            support_phi := fun i => (hts i).trans (hs (e i))
            smooth_phi := ?_
            neighborhood := {x | δ < S x}
            open_neighborhood := isOpen_lt continuous_const hS
            covers_compact := ?_
            partition := ?_ }⟩
  · intro i j
    have hSj : ContDiff ℝ (⊤ : ℕ∞) (fun z =>
        S (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j)
          (KPCuspSiegel.projection F _ z))) :=
      ContDiff.sum (fun k _ => hsm (e k) j)
    exact (hsm (e i) j).div (hD.comp hSj) (fun z =>
      ne_of_gt (hDpos _ (hS0 _)))
  · intro x hx
    change δ < S x
    have hh := haK x hx
    dsimp [δ]
    linarith
  · intro x hx
    change δ < S x at hx
    change (∑ i, bs i x / D (S x)) = 1
    rw [← Finset.sum_div, hDeq _ hx.le]
    exact div_self (ne_of_gt (hδ.trans hx))

end DedekindZetaZeroFree.CoreChartLocalizers.CutoffConstruction

end
