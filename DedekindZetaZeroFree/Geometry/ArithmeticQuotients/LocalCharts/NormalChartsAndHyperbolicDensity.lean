module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.LineBundleLocalization
public import DedekindZetaZeroFree.Geometry.Hyperbolic.Archimedean.RealCoordinatesAndVolume

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.CoreChartLocalizers.CutoffConstruction

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

private theorem invariant_neighborhood {G T : Type*} [Group G] [TopologicalSpace T]
    [MulAction G T] [ContinuousConstSMul G T] [T2Space T] [LocallyCompactSpace T]
    [ProperlyDiscontinuousSMul G T] (p : T) :
    ∃ V : Set T, IsOpen V ∧ p ∈ V ∧
      (∀ g : MulAction.stabilizer G p, (fun x => (g.val : G) • x) '' V = V) ∧
      (∀ g : G, ∀ x ∈ V, ∀ y ∈ V, g • x = y → g ∈ MulAction.stabilizer G p) := by
  letI : Finite (MulAction.stabilizer G p) :=
    (ProperlyDiscontinuousSMul.finite_stabilizer (Γ := G) p).to_subtype
  letI := Fintype.ofFinite (MulAction.stabilizer G p)
  obtain ⟨W, hW, hsep⟩ := ProperlyDiscontinuousSMul.exists_nhds_disjoint_image G p
  obtain ⟨W₀, hsub, hopen, hp⟩ := mem_nhds_iff.mp hW
  let V := ⋂ g : MulAction.stabilizer G p, (fun x => (g.val : G) • x) ⁻¹' W₀
  have hvopen : IsOpen V := isOpen_iInter_of_finite fun g =>
    hopen.preimage (continuous_const_smul (g.val : G))
  have hpv : p ∈ V := by
    apply Set.mem_iInter.mpr
    intro g
    change (g.val : G) • p ∈ W₀
    simpa only [MulAction.mem_stabilizer_iff.mp g.property] using hp
  have hvsub : V ⊆ W := by
    intro x hx
    apply hsub
    have hh := Set.mem_iInter.mp hx (1 : MulAction.stabilizer G p)
    simpa using hh
  refine ⟨V, hvopen, hpv, ?_, ?_⟩
  · intro g
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      apply Set.mem_iInter.mpr
      intro h
      change (h.val : G) • ((g.val : G) • y) ∈ W₀
      simpa only [Set.mem_preimage, Subgroup.coe_mul, Subgroup.coe_inv, ← mul_smul] using Set.mem_iInter.mp hy (h * g)
    · intro hx
      refine ⟨(g.val : G)⁻¹ • x, ?_, smul_inv_smul _ _⟩
      apply Set.mem_iInter.mpr
      intro h
      change (h.val : G) • ((g.val : G)⁻¹ • x) ∈ W₀
      simpa only [Set.mem_preimage, Subgroup.coe_mul, Subgroup.coe_inv, ← mul_smul] using Set.mem_iInter.mp hx (h * g⁻¹)
  · intro g x hx y hy hxy
    apply MulAction.mem_stabilizer_iff.mpr
    by_contra hnot
    have hd := hsep g hnot
    have : y ∈ (fun x => g • x) '' W ∩ W :=
      ⟨⟨x, hvsub hx, hxy⟩, hvsub hy⟩
    exact Set.disjoint_left.mp hd this.1 this.2

include hF in

theorem component_invariant_separated_neighborhood
    (g : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (p : KPFiniteCuspAtlas.SymmetricSpace F) :
    ∃ V : Set (KPFiniteCuspAtlas.SymmetricSpace F), IsOpen V ∧ p ∈ V ∧
      (∀ h : MulAction.stabilizer (KPCuspGenuineMonodromy.Component F ζ hζ U g) p,
        (fun x => (h.val : KPCuspArithmetic.PGL2 F) • x) '' V = V) ∧
      (∀ γ : KPCuspGenuineMonodromy.Component F ζ hζ U g,
        ∀ x ∈ V, ∀ y ∈ V, (γ : KPCuspArithmetic.PGL2 F) • x = y →
          γ ∈ MulAction.stabilizer _ p) := by
  letI : ContinuousConstSMul (KPCuspGenuineMonodromy.Component F ζ hζ U g)
      (KPArch.Space (KPCuspLogShape.dimension F)) :=
    ⟨fun γ => KPCuspSiegel.continuous_action F γ.val⟩
  letI : ProperlyDiscontinuousSMul (KPCuspGenuineMonodromy.Component F ζ hζ U g)
      (KPArch.Space (KPCuspLogShape.dimension F)) :=
    KPFiniteAdelicCuspEnds.FundamentalDomainGeometry.arithmeticStabilizer_properlyDiscontinuous_of_compact
      F hF _ (KPCuspGenuineMonodromy.finiteBase_level_compact F ζ hζ U)
      (KPCuspGenuineMonodromy.finiteBase F ζ hζ g)
  exact invariant_neighborhood (G := KPCuspGenuineMonodromy.Component F ζ hζ U g) p

theorem chart_image_open (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : Chart F ζ hζ hF U A) : IsOpen (C.O F ζ hζ hF U) := by
  letI : ContinuousConstSMul (KPCuspArithmetic.PGL2 F)
      (KPArch.Space (KPCuspLogShape.dimension F)) :=
    ⟨KPCuspSiegel.continuous_action F⟩
  have hball : Metric.ball (0 : E C.n) C.radius ⊆ C.extendedDomain :=
    fun _ hx => C.closed_ball_in_extension (subset_closure hx)
  have hrange : Set.range (Set.restrict C.extendedDomain C.coordinates) =
      C.coordinates '' C.extendedDomain := by
    ext y
    simp [Set.restrict]
  have hopen : IsOpenMap (Set.restrict C.extendedDomain C.coordinates) :=
    C.coordinates_embedding.isInducing.isOpenMap (hrange.symm ▸ C.coordinates_open)
  have hcoord : IsOpen (C.coordinates '' Metric.ball (0 : E C.n) C.radius) := by
    have hh := hopen (Subtype.val ⁻¹' Metric.ball (0 : E C.n) C.radius)
      (Metric.isOpen_ball.preimage continuous_subtype_val)
    convert hh using 1
    ext y
    simp only [Set.mem_image, Set.mem_preimage, Set.restrict]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hball hv⟩, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.val, hv, rfl⟩
  letI : ContinuousConstSMul (KPCuspGenuineMonodromy.Component F ζ hζ U
      (A.representative C.component)) (KPArch.Space (KPCuspLogShape.dimension F)) :=
    ⟨fun γ => KPCuspSiegel.continuous_action F γ.val⟩
  have hproj : IsOpenMap (KPCuspSiegel.projection F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component))) :=
    isOpenMap_quotient_mk'_mul
  have hcomponent : IsOpenMap (KPFiniteCuspAtlas.componentMap F ζ hζ U
      (A.representative C.component)) := by
    have hh := A.components.isOpenMap.comp
      (isOpenMap_sigmaMk (i := C.component))
    convert hh using 1
    funext q
    exact (A.components_formula C.component q).symm
  have hh := hcomponent _ (hproj _ hcoord)
  change IsOpen ((fun x => KPFiniteCuspAtlas.componentMap F ζ hζ U
    (A.representative C.component) (KPCuspSiegel.projection F _ (C.coordinates x))) ''
    Metric.ball (0 : E C.n) C.radius)
  simpa only [Set.image_image, Function.comp_def] using hh

namespace StabilizerLinearization

variable (F : Type) [Field F] [NumberField F]

lemma rational_action_contDiff (γ : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : KPArch.Space (KPCuspLogShape.dimension F) => γ • p) := by
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  have he : (fun p : KPArch.Space (KPCuspLogShape.dimension F) =>
      (Matrix.ProjGenLinGroup.mk B : KPCuspArithmetic.PGL2 F) • p) = KPCuspSiegel.glAction F B := by
    funext p
    exact KPCuspSiegel.action_mk F B p
  rw [he]
  exact (KPArch.productAction_contDiff (KPCuspLogShape.dimension F)
      (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding B)).of_le le_top
variable (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
variable (p : KPArch.Space (KPCuspLogShape.dimension F))

def stabilizerDifferential : MulAction.stabilizer Γ p →*
    (KPArch.Space (KPCuspLogShape.dimension F) →L[ℝ] KPArch.Space (KPCuspLogShape.dimension F)) where
  toFun g := fderiv ℝ (fun q => (g.val.val : KPCuspArithmetic.PGL2 F) • q) p
  map_one' := by
    simp only [OneMemClass.coe_one, Subgroup.coe_one, one_smul]
    change fderiv ℝ id p = 1
    rw [fderiv_id]
    rfl
  map_mul' g h := by
    have hg := (rational_action_contDiff F g.val.val).differentiable (by simp) (h.val.val • p)
    have hh := (rational_action_contDiff F h.val.val).differentiable (by simp) p
    have hp : (h.val.val : KPCuspArithmetic.PGL2 F) • p = p :=
      MulAction.mem_stabilizer_iff.mp h.property
    change fderiv ℝ (fun q => (g.val.val * h.val.val : KPCuspArithmetic.PGL2 F) • q) p = _
    simp only [mul_smul]
    change fderiv ℝ ((fun q => (g.val.val : KPCuspArithmetic.PGL2 F) • q) ∘
      (fun q => (h.val.val : KPCuspArithmetic.PGL2 F) • q)) p = _
    rw [fderiv_comp p hg hh, hp]
    rfl
variable [Fintype (MulAction.stabilizer Γ p)]

def averagedStabilizerCoordinates (q : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPArch.Space (KPCuspLogShape.dimension F) :=
  (Fintype.card (MulAction.stabilizer Γ p) : ℝ)⁻¹ •
    ∑ g : MulAction.stabilizer Γ p,
      stabilizerDifferential F Γ p g⁻¹ ((g.val.val : KPCuspArithmetic.PGL2 F) • q - p)

lemma averagedStabilizerCoordinates_center : averagedStabilizerCoordinates F Γ p p = 0 := by
  unfold averagedStabilizerCoordinates
  have hp (g : MulAction.stabilizer Γ p) : (g.val.val : KPCuspArithmetic.PGL2 F) • p = p :=
    MulAction.mem_stabilizer_iff.mp g.property
  simp only [hp, sub_self, map_zero, Finset.sum_const_zero, smul_zero]

lemma averagedStabilizerCoordinates_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (averagedStabilizerCoordinates F Γ p) := by
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro g _
  exact (stabilizerDifferential F Γ p g⁻¹).contDiff.comp
    ((rational_action_contDiff F g.val.val).sub contDiff_const)

lemma averagedStabilizerCoordinates_hasFDerivAt :
    HasFDerivAt (averagedStabilizerCoordinates F Γ p)
      (ContinuousLinearMap.id ℝ (KPArch.Space (KPCuspLogShape.dimension F))) p := by
  have hh (g : MulAction.stabilizer Γ p) :
      HasFDerivAt (fun q => stabilizerDifferential F Γ p g⁻¹
          ((g.val.val : KPCuspArithmetic.PGL2 F) • q - p))
        (ContinuousLinearMap.id ℝ (KPArch.Space (KPCuspLogShape.dimension F))) p := by
    have hi := (((rational_action_contDiff F g.val.val).differentiable (by simp) p).hasFDerivAt.sub_const p)
    have hd := ((stabilizerDifferential F Γ p g⁻¹).hasFDerivAt
      (x := (g.val.val : KPCuspArithmetic.PGL2 F) • p - p)).comp p
        (f := fun q => (g.val.val : KPCuspArithmetic.PGL2 F) • q - p) hi
    have he : (stabilizerDifferential F Γ p g⁻¹).comp
        (fderiv ℝ (fun q => (g.val.val : KPCuspArithmetic.PGL2 F) • q) p) =
        ContinuousLinearMap.id ℝ (KPArch.Space (KPCuspLogShape.dimension F)) := by
      change stabilizerDifferential F Γ p g⁻¹ * stabilizerDifferential F Γ p g = 1
      simp only [← map_mul, inv_mul_cancel, map_one]
    rw [he] at hd
    exact hd
  have hs := (HasFDerivAt.sum (u := Finset.univ) (fun g _ => hh g)).const_smul
    (Fintype.card (MulAction.stabilizer Γ p) : ℝ)⁻¹
  convert hs using 1
  · funext q
    simp [averagedStabilizerCoordinates, Finset.sum_apply]
  · simp only [Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [Fintype.card_ne_zero]

lemma averagedStabilizerCoordinates_equivariant
    (h : MulAction.stabilizer Γ p) (q : KPArch.Space (KPCuspLogShape.dimension F)) :
    averagedStabilizerCoordinates F Γ p ((h.val.val : KPCuspArithmetic.PGL2 F) • q) =
      stabilizerDifferential F Γ p h (averagedStabilizerCoordinates F Γ p q) := by
  unfold averagedStabilizerCoordinates
  rw [map_smul, map_sum]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulRight h)
  intro g
  change stabilizerDifferential F Γ p g⁻¹ (g.val.val • (h.val.val • q) - p) =
    stabilizerDifferential F Γ p h (stabilizerDifferential F Γ p (g * h)⁻¹
      ((g * h).val.val • q - p))
  have he : h * (g * h)⁻¹ = g⁻¹ := by group
  have hd := congrArg (fun L : KPArch.Space (KPCuspLogShape.dimension F) →L[ℝ] _ =>
    L ((g.val.val * h.val.val : KPCuspArithmetic.PGL2 F) • q - p))
      ((stabilizerDifferential F Γ p).map_mul h (g * h)⁻¹)
  rw [he] at hd
  simpa only [ContinuousLinearMap.mul_apply, Subgroup.coe_mul, mul_smul] using hd

lemma averagedStabilizerCoordinates_local_inverse :
    ∃ e : OpenPartialHomeomorph (KPArch.Space (KPCuspLogShape.dimension F))
        (KPArch.Space (KPCuspLogShape.dimension F)),
      (e : _ → _) = averagedStabilizerCoordinates F Γ p ∧
      p ∈ e.source ∧ (0 : KPArch.Space (KPCuspLogShape.dimension F)) ∈ e.target ∧
      e.symm 0 = p ∧ ContDiffAt ℝ (⊤ : ℕ∞) e.symm 0 := by
  let f := averagedStabilizerCoordinates F Γ p
  have hf := (averagedStabilizerCoordinates_smooth F Γ p).contDiffAt (x := p)
  have hd : HasFDerivAt f
      (ContinuousLinearEquiv.refl ℝ (KPArch.Space (KPCuspLogShape.dimension F)) : _ →L[ℝ] _) p :=
    averagedStabilizerCoordinates_hasFDerivAt F Γ p
  have hn : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  let e := hf.toOpenPartialHomeomorph f hd hn
  have he : (e : _ → _) = f := hf.toOpenPartialHomeomorph_coe hd hn
  have hc : f p = 0 := averagedStabilizerCoordinates_center F Γ p
  have hp : p ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hd hn
  refine ⟨e, he, hp, ?_, ?_, ?_⟩
  · simpa only [he, hc] using e.map_source hp
  · have h := e.left_inv hp
    simpa only [he, hc] using h
  · have hs := hf.to_localInverse hd hn
    change ContDiffAt ℝ (⊤ : ℕ∞) (hf.localInverse hd hn) 0
    simpa only [averagedStabilizerCoordinates_center] using hs

lemma averagedStabilizerCoordinates_smooth_local_inverse :
    ∃ e : OpenPartialHomeomorph (KPArch.Space (KPCuspLogShape.dimension F))
        (KPArch.Space (KPCuspLogShape.dimension F)),
      (e : _ → _) = averagedStabilizerCoordinates F Γ p ∧
      p ∈ e.source ∧ (0 : KPArch.Space (KPCuspLogShape.dimension F)) ∈ e.target ∧
      e.symm 0 = p ∧ ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
      (∀ q ∈ e.source, (fderiv ℝ (averagedStabilizerCoordinates F Γ p) q).IsInvertible) := by
  obtain ⟨e, he, hp, h0, hc, _⟩ := averagedStabilizerCoordinates_local_inverse F Γ p
  let f := averagedStabilizerCoordinates F Γ p
  let D := {q | (fderiv ℝ f q).IsInvertible}
  have hf := averagedStabilizerCoordinates_smooth F Γ p
  have hD : IsOpen D := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
    (hf.continuous_fderiv (by simp))
  have hpD : p ∈ D := by
    change (fderiv ℝ f p).IsInvertible
    rw [(averagedStabilizerCoordinates_hasFDerivAt F Γ p).fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  let e' := e.restrOpen D hD
  have he' : (e' : _ → _) = f := he
  have hp' : p ∈ e'.source := ⟨hp, hpD⟩
  have hf0 : f p = 0 := averagedStabilizerCoordinates_center F Γ p
  refine ⟨e', he', hp', ?_, ?_, ?_, ?_⟩
  · simpa only [he', hf0] using e'.map_source hp'
  · simpa only [he', hf0] using e'.left_inv hp'
  · intro q hq
    have hqD : e'.symm q ∈ D := (e'.map_target hq).2
    obtain ⟨L, hL⟩ := hqD
    apply (e'.contDiffAt_symm hq (f₀' := L) ?_ ?_).contDiffWithinAt
    · rw [he', hL]
      exact (hf.differentiable (by simp) _).hasFDerivAt
    · rw [he']
      exact hf.contDiffAt
  · intro q hq
    exact hq.2

private lemma invariant_smooth_inverse (V : Set (KPArch.Space (KPCuspLogShape.dimension F)))
    (hV : IsOpen V) (hpV : p ∈ V) :
    ∃ e : OpenPartialHomeomorph (KPArch.Space (KPCuspLogShape.dimension F))
        (KPArch.Space (KPCuspLogShape.dimension F)),
      (e : _ → _) = averagedStabilizerCoordinates F Γ p ∧
      p ∈ e.source ∧ (0 : KPArch.Space (KPCuspLogShape.dimension F)) ∈ e.target ∧
      e.symm 0 = p ∧ ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
      (∀ q ∈ e.source, (fderiv ℝ (averagedStabilizerCoordinates F Γ p) q).IsInvertible) ∧
      e.source ⊆ V ∧
      (∀ g : MulAction.stabilizer Γ p,
        (fun q => (g.val.val : KPCuspArithmetic.PGL2 F) • q) '' e.source = e.source) ∧
      (∀ g : MulAction.stabilizer Γ p,
        stabilizerDifferential F Γ p g '' e.target = e.target) ∧
      (∀ g : MulAction.stabilizer Γ p, ∀ q ∈ e.target,
        e.symm (stabilizerDifferential F Γ p g q) =
          (g.val.val : KPCuspArithmetic.PGL2 F) • e.symm q) := by
  obtain ⟨e, he, hp, h0, hc, hs, hd⟩ := averagedStabilizerCoordinates_smooth_local_inverse F Γ p
  let W := ⋂ g : MulAction.stabilizer Γ p,
    (fun q => (g.val.val : KPCuspArithmetic.PGL2 F) • q) ⁻¹' (e.source ∩ V)
  have hW : IsOpen W := isOpen_iInter_of_finite fun g =>
    (e.open_source.inter hV).preimage (rational_action_contDiff F g.val.val).continuous
  have hpW : p ∈ W := by
    apply Set.mem_iInter.mpr
    intro g
    change (g.val.val : KPCuspArithmetic.PGL2 F) • p ∈ e.source ∩ V
    have hg : (g.val.val : KPCuspArithmetic.PGL2 F) • p = p :=
      MulAction.mem_stabilizer_iff.mp g.property
    rw [hg]
    exact ⟨hp, hpV⟩
  have hWsub : W ⊆ e.source ∩ V := by
    intro q hq
    have h := Set.mem_iInter.mp hq (1 : MulAction.stabilizer Γ p)
    simpa using h
  have hWsmul (g : MulAction.stabilizer Γ p) {q} (hq : q ∈ W) :
      (g.val.val : KPCuspArithmetic.PGL2 F) • q ∈ W := by
    apply Set.mem_iInter.mpr
    intro h
    change (h.val.val : KPCuspArithmetic.PGL2 F) •
      ((g.val.val : KPCuspArithmetic.PGL2 F) • q) ∈ e.source ∩ V
    simpa only [Set.mem_preimage, Subgroup.coe_mul, ← mul_smul] using
      Set.mem_iInter.mp hq (h * g)
  let e' := e.restrOpen W hW
  have he' : (e' : _ → _) = averagedStabilizerCoordinates F Γ p := he
  have hsource : e'.source = W := Set.inter_eq_right.mpr (fun q hq => (hWsub hq).1)
  have hp' : p ∈ e'.source := hsource.symm ▸ hpW
  have hf0 := averagedStabilizerCoordinates_center F Γ p
  have hsource_smul (g : MulAction.stabilizer Γ p) {q} (hq : q ∈ e'.source) :
      (g.val.val : KPCuspArithmetic.PGL2 F) • q ∈ e'.source := by
    rw [hsource] at hq ⊢
    exact hWsmul g hq
  have htarget (q) (hq : q ∈ e'.target) : q ∈ e.target := by
    have hx := e'.map_target hq
    have h := e.map_source hx.1
    have hinv : (e' : _ → _) (e'.symm q) = q := e'.right_inv hq
    rw [← hinv]
    exact h
  have htarget_smul (g : MulAction.stabilizer Γ p) {q} (hq : q ∈ e'.target) :
      stabilizerDifferential F Γ p g q ∈ e'.target := by
    have hinv := e'.right_inv hq
    rw [he'] at hinv
    rw [← hinv, ← averagedStabilizerCoordinates_equivariant]
    exact he' ▸ e'.map_source (hsource_smul g (e'.map_target hq))
  refine ⟨e', he', hp', ?_, ?_, ?_, (fun q hq => hd q hq.1), ?_, ?_, ?_, ?_⟩
  · simpa only [he', hf0] using e'.map_source hp'
  · simpa only [he', hf0] using e'.left_inv hp'
  · exact hs.mono htarget
  · intro q hq
    exact (hWsub (hsource ▸ hq)).2
  · intro g
    ext q
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hsource_smul g hv
    · intro hq
      refine ⟨(g.val.val : KPCuspArithmetic.PGL2 F)⁻¹ • q, ?_, smul_inv_smul _ _⟩
      exact hsource_smul g⁻¹ hq
  · intro g
    ext q
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact htarget_smul g hv
    · intro hq
      refine ⟨stabilizerDifferential F Γ p g⁻¹ q, htarget_smul g⁻¹ hq, ?_⟩
      change (stabilizerDifferential F Γ p g * stabilizerDifferential F Γ p g⁻¹) q = q
      simp only [← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
  · intro g q hq
    apply e'.injOn (e'.map_target (htarget_smul g hq))
      (hsource_smul g (e'.map_target hq))
    rw [e'.right_inv (htarget_smul g hq), he',
      averagedStabilizerCoordinates_equivariant]
    have hh := e'.right_inv hq
    rw [he'] at hh
    rw [hh]

def tangentFrame (d : ℕ) (p : KPArch.Space d) :
    E (3 * d) ≃L[ℝ] KPArch.Space d :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun x i =>
      (KPArch.height (p i) •
        (⟨x ((finProdFinEquiv.trans (finCongr (Nat.mul_comm d 3))) (i, 0)),
          x ((finProdFinEquiv.trans (finCongr (Nat.mul_comm d 3))) (i, 1))⟩ : ℂ),
        x ((finProdFinEquiv.trans (finCongr (Nat.mul_comm d 3))) (i, 2)))
    invFun := fun v => WithLp.toLp 2 (fun k =>
      let ik := (finProdFinEquiv.trans (finCongr (Nat.mul_comm d 3))).symm k
      if ik.2 = 0 then (KPArch.height (p ik.1))⁻¹ * (v ik.1).1.re
      else if ik.2 = 1 then (KPArch.height (p ik.1))⁻¹ * (v ik.1).1.im
      else (v ik.1).2)
    left_inv := by
      intro x
      apply PiLp.ext
      intro k
      obtain ⟨⟨i,j⟩, rfl⟩ :=
        (finProdFinEquiv.trans (finCongr (Nat.mul_comm d 3))).surjective k
      fin_cases j <;> simp [show KPArch.height (p i) ≠ 0 from Real.exp_ne_zero _, ← mul_assoc]
    right_inv := by
      intro v
      funext i
      apply Prod.ext
      · apply Complex.ext <;> simp [show KPArch.height (p i) ≠ 0 from Real.exp_ne_zero _, ← mul_assoc]
      · simp
    map_add' := by
      intro x y
      funext i
      apply Prod.ext
      · apply Complex.ext <;> simp [mul_add]
      · simp
    map_smul' := by
      intro r x
      funext i
      apply Prod.ext
      · apply Complex.ext <;> simp <;> ring
      · simp }

lemma tangentFrame_metric (d : ℕ) (p : KPArch.Space d) (x : E (3 * d)) :
    KPArch.metric d p (tangentFrame d p x) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [← Fintype.sum_equiv
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm d 3)))
    (fun ij : Fin d × Fin 3 => x ((finProdFinEquiv.trans (finCongr (Nat.mul_comm d 3))) ij) ^ 2)
    (fun k => x k ^ 2) (fun _ => rfl), Fintype.sum_prod_type]
  unfold KPArch.metric
  apply Finset.sum_congr rfl
  intro i _
  change (KPArch.height (p i))⁻¹ ^ 2 *
      ‖KPArch.height (p i) • (⟨x ((finProdFinEquiv.trans (finCongr (Nat.mul_comm d 3))) (i, 0)),
        x ((finProdFinEquiv.trans (finCongr (Nat.mul_comm d 3))) (i, 1))⟩ : ℂ)‖ ^ 2 +
      x ((finProdFinEquiv.trans (finCongr (Nat.mul_comm d 3))) (i, 2)) ^ 2 = _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Fin.sum_univ_three]
  have h : KPArch.height (p i) ≠ 0 := Real.exp_ne_zero _
  field_simp
  <;> ring

lemma stabilizerDifferential_metric (h : MulAction.stabilizer Γ p)
    (v : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPArch.metric _ p (stabilizerDifferential F Γ p h v) = KPArch.metric _ p v := by
  obtain ⟨B, hB⟩ := Matrix.ProjGenLinGroup.mk_surjective h.val.val
  have he : (fun q : KPArch.Space (KPCuspLogShape.dimension F) =>
      (h.val.val : KPCuspArithmetic.PGL2 F) • q) =
      KPArch.productAction _ (fun i => Matrix.GeneralLinearGroup.map
        (KPCusp.complexPlace F i).embedding B) := by
    funext q
    rw [← hB]
    exact KPCuspSiegel.action_mk F B q
  have hp : KPArch.productAction _ (fun i => Matrix.GeneralLinearGroup.map
      (KPCusp.complexPlace F i).embedding B) p = p := by
    rw [← he]
    exact MulAction.mem_stabilizer_iff.mp h.property
  have hm := KPArch.metric_invariant _
    (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding B) p v
  rw [hp] at hm
  simpa only [stabilizerDifferential, MonoidHom.coe_mk, OneHom.coe_mk, he] using hm

def stabilizerDifferentialEquiv (h : MulAction.stabilizer Γ p) :
    KPArch.Space (KPCuspLogShape.dimension F) ≃L[ℝ]
      KPArch.Space (KPCuspLogShape.dimension F) :=
  LinearEquiv.toContinuousLinearEquiv {
    toLinearMap := (stabilizerDifferential F Γ p h).toLinearMap
    invFun := stabilizerDifferential F Γ p h⁻¹
    left_inv := by
      intro v
      change (stabilizerDifferential F Γ p h⁻¹ * stabilizerDifferential F Γ p h) v = v
      simp only [← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
    right_inv := by
      intro v
      change (stabilizerDifferential F Γ p h * stabilizerDifferential F Γ p h⁻¹) v = v
      simp only [← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply] }

def stabilizerOrthogonal : MulAction.stabilizer Γ p →*
    (E (3 * KPCuspLogShape.dimension F) ≃ₗᵢ[ℝ] E (3 * KPCuspLogShape.dimension F)) where
  toFun h := {
    toLinearEquiv := ((tangentFrame _ p).trans
      ((stabilizerDifferentialEquiv F Γ p h).trans (tangentFrame _ p).symm)).toLinearEquiv
    norm_map' := by
      intro x
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change ‖(tangentFrame _ p).symm (stabilizerDifferential F Γ p h (tangentFrame _ p x))‖ ^ 2 = ‖x‖ ^ 2
      rw [← tangentFrame_metric _ p]
      rw [(tangentFrame _ p).apply_symm_apply, stabilizerDifferential_metric, tangentFrame_metric] }
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    change (tangentFrame _ p).symm (stabilizerDifferential F Γ p 1 (tangentFrame _ p x)) = x
    rw [map_one, ContinuousLinearMap.one_apply, (tangentFrame _ p).symm_apply_apply]
  map_mul' h k := by
    apply LinearIsometryEquiv.ext
    intro x
    change (tangentFrame _ p).symm (stabilizerDifferential F Γ p (h * k) (tangentFrame _ p x)) =
      (tangentFrame _ p).symm (stabilizerDifferential F Γ p h
        (tangentFrame _ p ((tangentFrame _ p).symm
          (stabilizerDifferential F Γ p k (tangentFrame _ p x)))))
    rw [map_mul, ContinuousLinearMap.mul_apply, (tangentFrame _ p).apply_symm_apply]

lemma tangentFrame_stabilizerOrthogonal (h : MulAction.stabilizer Γ p)
    (x : E (3 * KPCuspLogShape.dimension F)) :
    tangentFrame _ p (stabilizerOrthogonal F Γ p h x) =
      stabilizerDifferential F Γ p h (tangentFrame _ p x) := by
  exact (tangentFrame _ p).apply_symm_apply _

end StabilizerLinearization

include hF in

theorem component_invariant_separated_smooth_inverse
    (g : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (p : KPFiniteCuspAtlas.SymmetricSpace F) :
    ∃ (H : Fintype (MulAction.stabilizer
          (KPCuspGenuineMonodromy.Component F ζ hζ U g) p))
      (e : OpenPartialHomeomorph (KPFiniteCuspAtlas.SymmetricSpace F)
        (KPFiniteCuspAtlas.SymmetricSpace F)),
      (e : _ → _) = @StabilizerLinearization.averagedStabilizerCoordinates F _ _
        (KPCuspGenuineMonodromy.Component F ζ hζ U g) p H ∧
      p ∈ e.source ∧ (0 : KPFiniteCuspAtlas.SymmetricSpace F) ∈ e.target ∧
      e.symm 0 = p ∧ ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
      (∀ q ∈ e.source, (fderiv ℝ (e : _ → _) q).IsInvertible) ∧
      (∀ h : MulAction.stabilizer (KPCuspGenuineMonodromy.Component F ζ hζ U g) p,
        (fun q => (h.val.val : KPCuspArithmetic.PGL2 F) • q) '' e.source = e.source) ∧
      (∀ h : MulAction.stabilizer (KPCuspGenuineMonodromy.Component F ζ hζ U g) p,
        StabilizerLinearization.stabilizerDifferential F
          (KPCuspGenuineMonodromy.Component F ζ hζ U g) p h '' e.target = e.target) ∧
      (∀ h : MulAction.stabilizer (KPCuspGenuineMonodromy.Component F ζ hζ U g) p,
        ∀ q ∈ e.target,
          e.symm (StabilizerLinearization.stabilizerDifferential F
            (KPCuspGenuineMonodromy.Component F ζ hζ U g) p h q) =
          (h.val.val : KPCuspArithmetic.PGL2 F) • e.symm q) ∧
      (∀ γ : KPCuspGenuineMonodromy.Component F ζ hζ U g,
        ∀ q ∈ e.source, ∀ r ∈ e.source,
          (γ : KPCuspArithmetic.PGL2 F) • q = r → γ ∈ MulAction.stabilizer _ p) := by
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U g
  letI : ContinuousConstSMul Γ (KPArch.Space (KPCuspLogShape.dimension F)) :=
    ⟨fun γ => KPCuspSiegel.continuous_action F γ.val⟩
  letI : ProperlyDiscontinuousSMul Γ (KPArch.Space (KPCuspLogShape.dimension F)) :=
    KPFiniteAdelicCuspEnds.FundamentalDomainGeometry.arithmeticStabilizer_properlyDiscontinuous_of_compact
      F hF _ (KPCuspGenuineMonodromy.finiteBase_level_compact F ζ hζ U)
      (KPCuspGenuineMonodromy.finiteBase F ζ hζ g)
  letI : Finite (MulAction.stabilizer Γ p) :=
    (ProperlyDiscontinuousSMul.finite_stabilizer (Γ := Γ) p).to_subtype
  letI := Fintype.ofFinite (MulAction.stabilizer Γ p)
  obtain ⟨V, hV, hpV, _, hsep⟩ :=
    component_invariant_separated_neighborhood F ζ hζ hF U g p
  obtain ⟨e, he, hp, h0, hc, hs, hd, hsub, hsource, htarget, heq⟩ :=
    StabilizerLinearization.invariant_smooth_inverse F Γ p V hV hpV
  refine ⟨inferInstance, e, he, hp, h0, hc, hs, ?_, hsource, htarget, heq, ?_⟩
  · simpa only [he] using hd
  · intro γ q hq r hr hqr
    exact hsep γ q (hsub hq) r (hsub hr) hqr

include hF in

theorem component_orthogonal_separated_smooth_chart
    (g : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (p : KPFiniteCuspAtlas.SymmetricSpace F) :
    ∃ (H : Fintype (MulAction.stabilizer
          (KPCuspGenuineMonodromy.Component F ζ hζ U g) p))
      (c : OpenPartialHomeomorph (E (3 * KPCuspLogShape.dimension F))
        (KPFiniteCuspAtlas.SymmetricSpace F)),
      (0 : E (3 * KPCuspLogShape.dimension F)) ∈ c.source ∧ c 0 = p ∧
      ContDiffOn ℝ (⊤ : ℕ∞) c c.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) c.symm c.target ∧
      (∀ h : MulAction.stabilizer (KPCuspGenuineMonodromy.Component F ζ hζ U g) p,
        StabilizerLinearization.stabilizerOrthogonal F
          (KPCuspGenuineMonodromy.Component F ζ hζ U g) p h '' c.source = c.source) ∧
      (∀ h : MulAction.stabilizer (KPCuspGenuineMonodromy.Component F ζ hζ U g) p,
        ∀ x ∈ c.source,
          c (StabilizerLinearization.stabilizerOrthogonal F
            (KPCuspGenuineMonodromy.Component F ζ hζ U g) p h x) =
            (h.val.val : KPCuspArithmetic.PGL2 F) • c x) ∧
      (∀ γ : KPCuspGenuineMonodromy.Component F ζ hζ U g,
        ∀ q ∈ c.target, ∀ r ∈ c.target,
          (γ : KPCuspArithmetic.PGL2 F) • q = r → γ ∈ MulAction.stabilizer _ p) := by
  obtain ⟨H, e, he, hp, h0, hc, hs, hd, hsource, htarget, heq, hsep⟩ :=
    component_invariant_separated_smooth_inverse F ζ hζ hF U g p
  letI := H
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U g
  let L := StabilizerLinearization.tangentFrame (KPCuspLogShape.dimension F) p
  let c := L.toHomeomorph.toOpenPartialHomeomorph.trans e.symm
  have hcsource : c.source = L ⁻¹' e.target := by
    simp [c, OpenPartialHomeomorph.trans_source]
  have hctarget : c.target = e.source := by
    simp [c, OpenPartialHomeomorph.trans_target]
  have hcapply (x) : c x = e.symm (L x) := rfl
  have hcsymm (q) : c.symm q = L.symm (e q) := rfl
  refine ⟨H, c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcsource]
    simpa using h0
  · simpa only [hcapply, map_zero] using hc
  · change ContDiffOn ℝ (⊤ : ℕ∞) (e.symm ∘ L) c.source
    apply hs.comp L.contDiff.contDiffOn
    intro x hx
    simpa only [hcsource, Set.mem_preimage] using hx
  · change ContDiffOn ℝ (⊤ : ℕ∞) (L.symm ∘ e) c.target
    apply L.symm.contDiff.contDiffOn.comp
      (by rw [he]; exact (StabilizerLinearization.averagedStabilizerCoordinates_smooth F Γ p).contDiffOn)
    exact Set.mapsTo_univ _ _
  · intro h
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hcsource] at hy ⊢
      change L (StabilizerLinearization.stabilizerOrthogonal F Γ p h y) ∈ e.target
      rw [StabilizerLinearization.tangentFrame_stabilizerOrthogonal]
      exact htarget h ▸ Set.mem_image_of_mem _ hy
    · intro hx
      refine ⟨StabilizerLinearization.stabilizerOrthogonal F Γ p h⁻¹ x, ?_, ?_⟩
      · rw [hcsource] at hx ⊢
        change L (StabilizerLinearization.stabilizerOrthogonal F Γ p h⁻¹ x) ∈ e.target
        rw [StabilizerLinearization.tangentFrame_stabilizerOrthogonal]
        exact htarget h⁻¹ ▸ Set.mem_image_of_mem _ hx
      · change (StabilizerLinearization.stabilizerOrthogonal F Γ p h *
          StabilizerLinearization.stabilizerOrthogonal F Γ p h⁻¹) x = x
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl
  · intro h x hx
    rw [hcapply, StabilizerLinearization.tangentFrame_stabilizerOrthogonal, hcapply]
    exact heq h (L x) (by simpa only [hcsource, Set.mem_preimage] using hx)
  · simpa only [hctarget] using hsep

namespace ChartDensityConstruction

lemma volumeDensity_smooth (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (KPArch.volumeDensity d) := by
  unfold KPArch.volumeDensity KPArch.height
  apply contDiff_prod
  intro i hi
  exact ((((contDiff_apply ℝ KPArch.H3 i).snd).exp).inv (fun _ => Real.exp_ne_zero _)).pow 2

lemma volumeDensity_positive (d : ℕ) (p : KPArch.Space d) :
    0 < KPArch.volumeDensity d p := by
  unfold KPArch.volumeDensity KPArch.height
  exact Finset.prod_pos fun _ _ => pow_pos (inv_pos.mpr (Real.exp_pos _)) 2

lemma weighted_jacobian_pushforward {n : ℕ} {s : Set (E n)}
    {f : E n → E n} {f' : E n → E n →L[ℝ] E n}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : Set.InjOn f s) (g : E n → ℝ) :
    Measure.map f ((volume.restrict s).withDensity
      (fun x => ENNReal.ofReal (|(f' x).det| * g (f x)))) =
      (volume.withDensity (fun x => ENNReal.ofReal (g x))).restrict (f '' s) := by
  have hfm : AEMeasurable f (volume.restrict s) :=
    (show ContinuousOn f s from fun x hx =>
      (hf' x hx).continuousWithinAt).aemeasurable hs
  have hfw : AEMeasurable f ((volume.restrict s).withDensity
      (fun x => ENNReal.ofReal (|(f' x).det| * g (f x)))) :=
    hfm.mono_ac (withDensity_absolutelyContinuous _ _)
  have him : MeasurableSet (f '' s) :=
    measurable_image_of_fderivWithin hs hf' hf
  ext t ht
  rw [Measure.map_apply_of_aemeasurable hfw ht,
    withDensity_apply₀ _ (hfm.nullMeasurableSet_preimage ht),
    Measure.restrict_apply ht, withDensity_apply _ (ht.inter him)]
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hf' hf
    (t.indicator (fun x => ENNReal.ofReal (g x)))
  rw [lintegral_indicator ht, Measure.restrict_restrict ht] at hcv
  rw [hcv]
  rw [← lintegral_indicator₀ (hfm.nullMeasurableSet_preimage ht)]
  apply lintegral_congr
  intro x
  by_cases hx : f x ∈ t
  · simp [hx, ENNReal.ofReal_mul (abs_nonneg _)]
  · simp [hx]

lemma smooth_det {n : ℕ} {s : Set (E n)} {L : E n → (E n →L[ℝ] E n)}
    (hL : ContDiffOn ℝ (⊤ : ℕ∞) L s) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (L x).det) s := by
  have hm (i j : Fin n) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => L x (EuclideanSpace.single j 1) i) s := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn.comp
      (hL.clm_apply (contDiffOn_const (c := EuclideanSpace.single j 1))) (Set.mapsTo_univ _ _)
  have he (x : E n) : (L x).det =
      Matrix.det (fun i j : Fin n => L x (EuclideanSpace.single j 1) i) := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
    rfl
  have hefun : (fun x => (L x).det) = (fun x =>
      Matrix.det (fun i j : Fin n => L x (EuclideanSpace.single j 1) i)) := funext he
  have hexpand (x : E n) : Matrix.det (fun i j : Fin n => L x (EuclideanSpace.single j 1) i) =
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) *
        ∏ i, L x (EuclideanSpace.single i 1) (σ i) := Matrix.det_apply' _
  rw [hefun, funext hexpand]
  apply ContDiffOn.sum
  intro σ hσ
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro i hi
  exact hm _ _

lemma derivative_density_smooth {n : ℕ} {s : Set (E n)} (hs : IsOpen s)
    {f : E n → E n} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s)
    (hdet : ∀ x ∈ s, (fderiv ℝ f x).det ≠ 0)
    {g : E n → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => |(fderiv ℝ f x).det| * g (f x)) s := by
  exact ((smooth_det (hf.fderiv_of_isOpen hs (by simp))).abs hdet).mul
    (hg.contDiffOn.comp hf (Set.mapsTo_univ _ _))

lemma invertible_det_ne_zero {n : ℕ} {L : E n →L[ℝ] E n}
    (hL : L.IsInvertible) : L.det ≠ 0 := by
  obtain ⟨e, rfl⟩ := hL
  exact e.toLinearEquiv.isUnit_det'.ne_zero

lemma ball_subset_cube_interior (n : ℕ) {a : ℝ} :
    Metric.ball (0 : E n) a ⊆ interior (cube n a) := by
  apply interior_maximal _ Metric.isOpen_ball
  intro x hx j
  have hn : ‖x‖ < a := by simpa [dist_zero_right] using hx
  have hj : |x j| < a := lt_of_le_of_lt (PiLp.norm_apply_le x j) hn
  exact ⟨(abs_lt.mp hj).1.le, (abs_lt.mp hj).2.le⟩

lemma shrink_ball_with_density_bounds {n : ℕ} {D : Set (E n)}
    (hD : IsOpen D) (h0 : (0 : E n) ∈ D) {w : E n → ℝ}
    (hw : ContinuousOn w D) (hw₀ : ∀ x ∈ D, 0 < w x) :
    ∃ r a lower upper : ℝ, 0 < r ∧ 0 < a ∧ 0 < lower ∧
      closure (Metric.ball (0 : E n) r) ⊆ D ∧
      closure (Metric.ball (0 : E n) r) ⊆ interior (cube n a) ∧
      ∀ x ∈ closure (Metric.ball (0 : E n) r),
        lower ≤ w x ∧ w x ≤ upper := by
  obtain ⟨r, hr, hrD⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hD.mem_nhds h0)
  have hc : closure (Metric.ball (0 : E n) r) ⊆ Metric.closedBall 0 r :=
    Metric.closure_ball_subset_closedBall
  have hK : IsCompact (closure (Metric.ball (0 : E n) r)) :=
    (isCompact_closedBall (0 : E n) r).of_isClosed_subset isClosed_closure hc
  have hne : (closure (Metric.ball (0 : E n) r)).Nonempty :=
    ⟨0, subset_closure (Metric.mem_ball_self hr)⟩
  have hcont := hw.mono (hc.trans hrD)
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hcont
  obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hne hcont
  refine ⟨r, r + 1, w p, w q, hr, by linarith, hw₀ p (hrD (hc hp)),
    hc.trans hrD, ?_, fun x hx => ⟨hmin hx, hmax hx⟩⟩
  apply Set.Subset.trans hc
  apply Set.Subset.trans (Metric.closedBall_subset_ball (by linarith : r < r + 1))
  exact ball_subset_cube_interior n

 def coordinatesLinear (d : ℕ) : EuclideanSpace ℝ (Fin (d * 3)) ≃L[ℝ] KPArch.Space d :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := KPArchRealCoordinates.coordinates d
    invFun := (KPArchRealCoordinates.coordinates d).symm
    left_inv := (KPArchRealCoordinates.coordinates d).left_inv
    right_inv := (KPArchRealCoordinates.coordinates d).right_inv
    map_add' := by
      intro x y
      funext i
      apply Prod.ext
      · apply Complex.ext <;> simp [KPArchRealCoordinates.coordinates]
      · simp [KPArchRealCoordinates.coordinates]
    map_smul' := by
      intro r x
      funext i
      apply Prod.ext
      · apply Complex.ext <;> simp [KPArchRealCoordinates.coordinates]
      · simp [KPArchRealCoordinates.coordinates] }
 lemma coordinates_contDiff (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (KPArchRealCoordinates.coordinates d) :=
  (coordinatesLinear d).contDiff
 lemma coordinates_symm_contDiff (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (KPArchRealCoordinates.coordinates d).symm :=
  (coordinatesLinear d).symm.contDiff

lemma openPartial_fderiv_invertible {n : ℕ} (c : OpenPartialHomeomorph (E n) (E n))
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c c.source)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) c.symm c.target) :
    ∀ x ∈ c.source, (fderiv ℝ c x).IsInvertible := by
  intro x hx
  have hd := (hc x hx).differentiableWithinAt (by simp)
  have hd' := hd.differentiableAt (c.open_source.mem_nhds hx)
  have he := ((hi (c x) (c.map_source hx)).differentiableWithinAt (by simp)).differentiableAt
    (c.open_target.mem_nhds (c.map_source hx))
  have hleft : (fun y => c.symm (c y)) =ᶠ[𝓝 x] id := by
    filter_upwards [c.open_source.mem_nhds hx] with y hy
    exact c.left_inv hy
  have hright : (fun y => c (c.symm y)) =ᶠ[𝓝 (c x)] id := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hx)] with y hy
    exact c.right_inv hy
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := fderiv ℝ c.symm (c x))
  · have hcxi : DifferentiableAt ℝ c (c.symm (c x)) := by rwa [c.left_inv hx]
    have h := fderiv_comp (c x) hcxi he
    simp only [c.left_inv hx, Function.comp_def] at h
    rw [hright.fderiv_eq, fderiv_id] at h
    exact h.symm
  · have h := fderiv_comp x he hd'
    simp only [Function.comp_def] at h
    rw [hleft.fderiv_eq, fderiv_id] at h
    exact h.symm

lemma hyperbolic_jacobian_pushforward (d : ℕ) {s : Set (E (d * 3))}
    {c : E (d * 3) → KPArch.Space d} (hs : MeasurableSet s)
    (hc : ∀ x ∈ s, DifferentiableWithinAt ℝ c s x)
    (hinj : Set.InjOn c s) :
    Measure.map c ((volume.restrict s).withDensity (fun x => ENNReal.ofReal
      (|(fderivWithin ℝ ((KPArchRealCoordinates.coordinates d).symm ∘ c) s x).det| *
        KPArch.volumeDensity d (c x)))) =
      (KPArch.hyperbolicVolume d).restrict (c '' s) := by
  let f := (KPArchRealCoordinates.coordinates d).symm ∘ c
  have hf : ∀ x ∈ s, HasFDerivWithinAt f (fderivWithin ℝ f s x) s x := by
    intro x hx
    exact (((coordinates_symm_contDiff d).differentiable (by simp)
      (c x)).comp_differentiableWithinAt x (hc x hx)).hasFDerivWithinAt
  have hfi : Set.InjOn f s := fun x hx y hy h =>
    hinj hx hy ((KPArchRealCoordinates.coordinates d).symm.injective h)
  have hcv := weighted_jacobian_pushforward hs hf hfi (KPArchRealCoordinates.density d)
  have hm := congrArg (Measure.map (KPArchRealCoordinates.coordinates d)) hcv
  have hfeq : KPArchRealCoordinates.coordinates d ∘ f = c := by
    funext x
    exact (KPArchRealCoordinates.coordinates d).apply_symm_apply _
  have hfmeas : AEMeasurable f (volume.restrict s) :=
    (show ContinuousOn f s from fun x hx => (hf x hx).continuousWithinAt).aemeasurable hs
  rw [AEMeasurable.map_map_of_aemeasurable
      (KPArchRealCoordinates.coordinates d).continuous.measurable.aemeasurable
      (hfmeas.mono_ac (withDensity_absolutelyContinuous _ _)), hfeq] at hm
  have hpre : (KPArchRealCoordinates.coordinates d) ⁻¹' (c '' s) = f '' s := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      exact ⟨y, hy, (congrArg (KPArchRealCoordinates.coordinates d).symm he).trans
        ((KPArchRealCoordinates.coordinates d).symm_apply_apply x)⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, ((KPArchRealCoordinates.coordinates d).apply_symm_apply _).symm⟩
  have hr := (KPArchRealCoordinates.coordinates d).toMeasurableEquiv.restrict_map
    (volume.withDensity (fun x => ENNReal.ofReal (KPArchRealCoordinates.density d x))) (c '' s)
  change (Measure.map (KPArchRealCoordinates.coordinates d)
    (volume.withDensity (fun x => ENNReal.ofReal (KPArchRealCoordinates.density d x)))).restrict (c '' s) =
    Measure.map (KPArchRealCoordinates.coordinates d) ((volume.withDensity
      (fun x => ENNReal.ofReal (KPArchRealCoordinates.density d x))).restrict
      ((KPArchRealCoordinates.coordinates d) ⁻¹' (c '' s))) at hr
  rw [← hpre, ← hr, KPArchRealCoordinates.metric_volume] at hm
  simpa [f, KPArchRealCoordinates.density] using hm

lemma density_unique_on_open {n : ℕ} {D : Set (E n)} (hD : IsOpen D)
    {w v : E n → ℝ} (hw : ContinuousOn w D) (hv : ContinuousOn v D)
    (hw₀ : ∀ x ∈ D, 0 ≤ w x) (hv₀ : ∀ x ∈ D, 0 ≤ v x)
    (h : (volume.restrict D).withDensity (fun x => ENNReal.ofReal (w x)) =
      (volume.restrict D).withDensity (fun x => ENNReal.ofReal (v x))) :
    Set.EqOn w v D := by
  have he := (withDensity_eq_iff_of_sigmaFinite
    ((ENNReal.continuous_ofReal.comp_continuousOn hw).aemeasurable hD.measurableSet)
    ((ENNReal.continuous_ofReal.comp_continuousOn hv).aemeasurable hD.measurableSet)).mp h
  have he' := Measure.eqOn_open_of_ae_eq he hD
    (ENNReal.continuous_ofReal.comp_continuousOn hw)
    (ENNReal.continuous_ofReal.comp_continuousOn hv)
  intro x hx
  have heq := congrArg ENNReal.toReal (he' hx)
  simpa [ENNReal.toReal_ofReal (hw₀ x hx), ENNReal.toReal_ofReal (hv₀ x hx)] using heq

lemma orthogonal_density_pushforward {n : ℕ} (A : E n ≃ₗᵢ[ℝ] E n)
    {D : Set (E n)} (hD : MeasurableSet D) (hAD : A '' D = D)
    {w : E n → ℝ} (hw : ContinuousOn w D) :
    Measure.map A ((volume.restrict D).withDensity (fun x => ENNReal.ofReal (w (A x)))) =
      (volume.restrict D).withDensity (fun x => ENNReal.ofReal (w x)) := by
  have hp : A ⁻¹' D = D := by
    calc
      A ⁻¹' D = A ⁻¹' (A '' D) := congrArg (fun s => A ⁻¹' s) hAD.symm
      _ = D := Set.preimage_image_eq _ A.injective
  have hmp : MeasurePreserving A (volume.restrict D) (volume.restrict D) := by
    refine ⟨A.continuous.measurable, ?_⟩
    have h := A.toMeasurableEquiv.restrict_map volume D
    change (Measure.map A volume).restrict D = Measure.map A (volume.restrict (A ⁻¹' D)) at h
    rw [A.measurePreserving.map_eq, hp] at h
    exact h.symm
  ext t ht
  rw [Measure.map_apply A.continuous.measurable ht,
    withDensity_apply _ (A.continuous.measurable ht), withDensity_apply _ ht]
  rw [← lintegral_indicator ht]
  conv_rhs => rw [← hmp.map_eq]
  have hm : AEMeasurable (t.indicator (fun x => ENNReal.ofReal (w x))) (volume.restrict D) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn hw).aemeasurable hD).indicator ht
  have hm' : AEMeasurable (t.indicator (fun x => ENNReal.ofReal (w x)))
      (Measure.map A (volume.restrict D)) := by rwa [hmp.map_eq]
  conv_rhs => rw [lintegral_map' hm' A.continuous.measurable.aemeasurable]
  rw [← lintegral_indicator (A.continuous.measurable ht)]
  rfl

lemma partial_map_injective {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [MeasurableSpace α] [BorelSpace α] [MeasurableSpace β] [BorelSpace β]
    (c : OpenPartialHomeomorph α β) {μ ν : Measure α}
    (hμ : ∀ᵐ x ∂μ, x ∈ c.source) (hν : ∀ᵐ x ∂ν, x ∈ c.source)
    (h : Measure.map c μ = Measure.map c ν) : μ = ν := by
  have recover (m : Measure α) (hm : ∀ᵐ x ∂m, x ∈ c.source) :
      Measure.map c.symm (Measure.map c m) = m := by
    have hc : AEMeasurable c m :=
      (c.continuousOn.aemeasurable c.open_source.measurableSet).mono_measure
        (by rw [Measure.restrict_eq_self_of_ae_mem hm])
    have htarget : ∀ᵐ y ∂Measure.map c m, y ∈ c.target := by
      exact (ae_map_iff hc c.open_target.measurableSet).mpr
        (hm.mono fun x hx => c.map_source hx)
    have hi₀ : AEMeasurable c.symm ((Measure.map c m).restrict c.target) :=
      c.symm.continuousOn.aemeasurable c.open_target.measurableSet
    have hi : AEMeasurable c.symm (Measure.map c m) := by
      rwa [Measure.restrict_eq_self_of_ae_mem htarget] at hi₀
    rw [AEMeasurable.map_map_of_aemeasurable hi hc]
    have he : (c.symm ∘ c) =ᵐ[m] id := hm.mono fun x hx => c.left_inv hx
    rw [Measure.map_congr he, Measure.map_id]
  rw [← recover μ hμ, h, recover ν hν]

lemma orthogonal_density_invariant {n : ℕ} {β : Type*}
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    (c : OpenPartialHomeomorph (E n) β) (A : E n ≃ₗᵢ[ℝ] E n)
    (B : β ≃ₜ β) (ν : Measure β)
    (hB : Measure.map B ν = ν)
    (hAD : A '' c.source = c.source) (hBT : B '' c.target = c.target)
    (heq : ∀ x ∈ c.source, c (A x) = B (c x))
    {w : E n → ℝ} (hw : ContinuousOn w c.source)
    (hw₀ : ∀ x ∈ c.source, 0 ≤ w x)
    (hcv : Measure.map c ((volume.restrict c.source).withDensity
      (fun x => ENNReal.ofReal (w x))) = ν.restrict c.target) :
    ∀ x ∈ c.source, w (A x) = w x := by
  let μ := (volume.restrict c.source).withDensity (fun x => ENNReal.ofReal (w x))
  have hμ : ∀ᵐ x ∂μ, x ∈ c.source :=
    (ae_restrict_mem c.open_source.measurableSet).filter_mono
      (withDensity_absolutelyContinuous _ _).ae_le
  have hAμ : ∀ᵐ x ∂Measure.map A μ, x ∈ c.source := by
    exact (ae_map_iff A.continuous.measurable.aemeasurable c.open_source.measurableSet).mpr
      (hμ.mono fun x hx => hAD ▸ Set.mem_image_of_mem A hx)
  have hcm : AEMeasurable c μ := by
    have hh : AEMeasurable c (μ.restrict c.source) :=
      c.continuousOn.aemeasurable c.open_source.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hμ] at hh
  have hcmA : AEMeasurable c (Measure.map A μ) := by
    have hh : AEMeasurable c ((Measure.map A μ).restrict c.source) :=
      c.continuousOn.aemeasurable c.open_source.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hAμ] at hh
  have hpre : B ⁻¹' c.target = c.target := by
    calc
      _ = B ⁻¹' (B '' c.target) := congrArg (fun s => B ⁻¹' s) hBT.symm
      _ = _ := Set.preimage_image_eq _ B.injective
  have hν : Measure.map B (ν.restrict c.target) = ν.restrict c.target := by
    have hr := B.toMeasurableEquiv.restrict_map ν c.target
    change (Measure.map B ν).restrict c.target = Measure.map B (ν.restrict (B ⁻¹' c.target)) at hr
    rw [hB, hpre] at hr
    exact hr.symm
  have hmaps : Measure.map c (Measure.map A μ) = Measure.map c μ := by
    rw [AEMeasurable.map_map_of_aemeasurable hcmA A.continuous.measurable.aemeasurable]
    have he : (c ∘ A) =ᵐ[μ] (B ∘ c) := hμ.mono fun x hx => heq x hx
    rw [Measure.map_congr he, ← AEMeasurable.map_map_of_aemeasurable
      B.continuous.measurable.aemeasurable hcm, hcv, hν]
  have hm : Measure.map A μ = μ := partial_map_injective c hAμ hμ hmaps
  have hv : ContinuousOn (fun x => w (A x)) c.source :=
    hw.comp A.continuous.continuousOn (fun x hx => hAD ▸ Set.mem_image_of_mem A hx)
  have hv₀ : ∀ x ∈ c.source, 0 ≤ w (A x) :=
    fun x hx => hw₀ _ (hAD ▸ Set.mem_image_of_mem A hx)
  have ht := orthogonal_density_pushforward A c.open_source.measurableSet hAD hw
  have hsame : (volume.restrict c.source).withDensity (fun x => ENNReal.ofReal (w (A x))) = μ := by
    apply A.toMeasurableEquiv.measurableEmbedding.map_injective
    exact ht.trans hm.symm
  exact density_unique_on_open c.open_source hv hw hv₀ hw₀ hsame

def reorder (d : ℕ) : E (3*d) ≃ₗᵢ[ℝ] E (d*3) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (Nat.mul_comm 3 d))
def flattenThree (d : ℕ) : E (3*d) ≃L[ℝ] KPArch.Space d :=
  (reorder d).toContinuousLinearEquiv.trans (coordinatesLinear d)
lemma flattenThree_volume (d : ℕ) : Measure.map (flattenThree d) volume = volume := by
  have hm := Measure.map_map (coordinatesLinear d).continuous.measurable
    (reorder d).continuous.measurable (μ := volume)
  rw [(reorder d).measurePreserving.map_eq] at hm
  have hh : Measure.map (coordinatesLinear d) volume = volume := KPArchRealCoordinates.coordinate_volume d
  rw [hh] at hm
  exact hm.symm
lemma hyperbolic_jacobian_three (d : ℕ) {s : Set (E (3*d))}
    {c : E (3*d) → KPArch.Space d} (hs : MeasurableSet s)
    (hc : ∀ x ∈ s, DifferentiableWithinAt ℝ c s x)
    (hinj : Set.InjOn c s) :
    Measure.map c ((volume.restrict s).withDensity (fun x => ENNReal.ofReal
      (|(fderivWithin ℝ ((flattenThree d).symm ∘ c) s x).det| *
        KPArch.volumeDensity d (c x)))) =
      (KPArch.hyperbolicVolume d).restrict (c '' s) := by
  let L := flattenThree d
  let f := L.symm ∘ c
  let g := fun x => KPArch.volumeDensity d (L x)
  have hf : ∀ x ∈ s, HasFDerivWithinAt f (fderivWithin ℝ f s x) s x := by
    intro x hx
    exact ((L.symm.differentiable (c x)).comp_differentiableWithinAt x (hc x hx)).hasFDerivWithinAt
  have hfi : Set.InjOn f s := fun x hx y hy h => hinj hx hy (L.symm.injective h)
  have hm := congrArg (Measure.map L) (weighted_jacobian_pushforward hs hf hfi g)
  have hfmeas : AEMeasurable f (volume.restrict s) :=
    (show ContinuousOn f s from fun x hx => (hf x hx).continuousWithinAt).aemeasurable hs
  have hfeq : L ∘ f = c := by funext x; exact L.apply_symm_apply _
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable
    (hfmeas.mono_ac (withDensity_absolutelyContinuous _ _)), hfeq] at hm
  have hpre : L ⁻¹' (c '' s) = f '' s := by
    ext x
    constructor
    · rintro ⟨y,hy,he⟩
      exact ⟨y,hy,(congrArg L.symm he).trans (L.symm_apply_apply x)⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,hy,(L.apply_symm_apply _).symm⟩
  have hr := L.toHomeomorph.toMeasurableEquiv.restrict_map
    (volume.withDensity (fun x => ENNReal.ofReal (g x))) (c '' s)
  change (Measure.map L (volume.withDensity (fun x => ENNReal.ofReal (g x)))).restrict (c '' s) =
    Measure.map L ((volume.withDensity (fun x => ENNReal.ofReal (g x))).restrict (L ⁻¹' (c '' s))) at hr
  have hmetric : Measure.map L (volume.withDensity (fun x => ENNReal.ofReal (g x))) = KPArch.hyperbolicVolume d := by
    ext t ht
    rw [Measure.map_apply L.continuous.measurable ht, withDensity_apply _ (L.continuous.measurable ht),
      KPArch.hyperbolicVolume, withDensity_apply _ ht]
    have hh := flattenThree_volume d
    rw [← lintegral_indicator ht, ← hh]
    have hg : Measurable (t.indicator (fun x => ENNReal.ofReal (KPArch.volumeDensity d x))) :=
      (ENNReal.measurable_ofReal.comp (volumeDensity_smooth d).continuous.measurable).indicator ht
    rw [lintegral_map hg L.continuous.measurable, ← lintegral_indicator (L.continuous.measurable ht)]
    rfl
  rw [← hpre, ← hr, hmetric] at hm
  simpa [f,g] using hm

end ChartDensityConstruction

lemma action_volume (γ : KPCuspArithmetic.PGL2 F) :
    Measure.map (fun p : KPArch.Space (KPCuspLogShape.dimension F) => γ • p)
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) =
      KPArch.hyperbolicVolume (KPCuspLogShape.dimension F) := by
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  have he : (fun p : KPArch.Space (KPCuspLogShape.dimension F) =>
      (Matrix.ProjGenLinGroup.mk B : KPCuspArithmetic.PGL2 F) • p) = KPCuspSiegel.glAction F B := by
    funext p
    exact KPCuspSiegel.action_mk F B p
  rw [he]
  exact KPArch.hyperbolicVolume_invariant _ _

open ChartDensityConstruction in
set_option maxHeartbeats 1000000 in
lemma component_chart (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (i : Fin A.componentCount) (p : KPFiniteCuspAtlas.SymmetricSpace F) :
    ∃ C : Chart F ζ hζ hF U A, C.component = i ∧ C.center = p := by
  have hc0 := component_orthogonal_separated_smooth_chart F ζ hζ hF U (A.representative i) p
  obtain ⟨H,c,h0,hp,hs,hi,hsource,heq,hsep⟩ := hc0
  have himage : (c : _ → _) '' c.source = c.target := c.toPartialHomeomorph.image_source_eq_target
  letI := H
  letI : ContinuousConstSMul (KPCuspArithmetic.PGL2 F) (KPArch.Space (KPCuspLogShape.dimension F)) :=
    ⟨KPCuspSiegel.continuous_action F⟩
  let d := KPCuspLogShape.dimension F
  let L := flattenThree d
  let f := L.symm ∘ c
  let e : OpenPartialHomeomorph (E (3*d)) (E (3*d)) := c.trans L.symm.toHomeomorph.toOpenPartialHomeomorph
  have hes : e.source = c.source := by simp [e, OpenPartialHomeomorph.trans_source]
  have hef (x) : e x = f x := rfl
  have heinv (x) : e.symm x = c.symm (L x) := rfl
  have hfs : ContDiffOn ℝ (⊤ : ℕ∞) f c.source :=
    L.symm.contDiff.contDiffOn.comp hs (Set.mapsTo_univ _ _)
  have hies : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target := by
    change ContDiffOn ℝ (⊤ : ℕ∞) (c.symm ∘ L) e.target
    apply hi.comp L.contDiff.contDiffOn
    intro x hx
    exact hx.2
  have hdet : ∀ x ∈ c.source, (fderiv ℝ f x).det ≠ 0 := by
    intro x hx
    apply invertible_det_ne_zero
    have hh := openPartial_fderiv_invertible e (by change ContDiffOn ℝ (⊤ : ℕ∞) f e.source; rwa [hes]) hies x (hes ▸ hx)
    exact hh
  let w := fun x => |(fderiv ℝ f x).det| * KPArch.volumeDensity d (c x)
  have hws : ContDiffOn ℝ (⊤ : ℕ∞) w c.source := by
    exact ((smooth_det (hfs.fderiv_of_isOpen c.open_source (by simp))).abs hdet).mul
      ((volumeDensity_smooth d).contDiffOn.comp hs (Set.mapsTo_univ _ _))
  have hwpos : ∀ x ∈ c.source, 0 < w x := fun x hx =>
    mul_pos (abs_pos.mpr (hdet x hx)) (volumeDensity_positive d _)
  have hcv : Measure.map c ((volume.restrict c.source).withDensity
      (fun x => ENNReal.ofReal (w x))) = (KPArch.hyperbolicVolume d).restrict c.target := by
    have hh := hyperbolic_jacobian_three d c.open_source.measurableSet
      (fun x hx => (hs x hx).differentiableWithinAt (by simp)) c.injOn
    rw [himage] at hh
    have heder : ∀ x ∈ c.source, fderivWithin ℝ f c.source x = fderiv ℝ f x :=
      fun x hx => fderivWithin_of_isOpen c.open_source hx
    convert hh using 1
    apply congrArg (Measure.map c)
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem c.open_source.measurableSet] with x hx
    simp only [w, ← heder x hx]
    rfl
  have hwinv : ∀ g : MulAction.stabilizer (KPCuspGenuineMonodromy.Component F ζ hζ U
        (A.representative i)) p, ∀ x ∈ c.source,
      w (StabilizerLinearization.stabilizerOrthogonal F _ p g x) = w x := by
    intro g
    let B : KPArch.Space d ≃ₜ KPArch.Space d := Homeomorph.smul (g.val.val : KPCuspArithmetic.PGL2 F)
    apply orthogonal_density_invariant c
      (StabilizerLinearization.stabilizerOrthogonal F _ p g) B (KPArch.hyperbolicVolume d)
      (show Measure.map B (KPArch.hyperbolicVolume d) = KPArch.hyperbolicVolume d from action_volume F g.val.val) (hsource g) ?_ (heq g) hws.continuousOn
      (fun x hx => (hwpos x hx).le) hcv
    ext q
    constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨x,hx,rfl⟩ := himage.symm ▸ hr
      change (g.val.val : KPCuspArithmetic.PGL2 F) • c x ∈ c.target
      rw [← heq g x hx]
      exact c.map_source (hsource g ▸ Set.mem_image_of_mem _ hx)
    · intro hq
      obtain ⟨x,hx,rfl⟩ := himage.symm ▸ hq
      refine ⟨c (StabilizerLinearization.stabilizerOrthogonal F _ p g⁻¹ x),
        c.map_source (hsource g⁻¹ ▸ Set.mem_image_of_mem _ hx), ?_⟩
      rw [heq g⁻¹ x hx]
      change g.val.val • (g.val.val⁻¹ • c x) = c x
      simp
  obtain ⟨r,a,lo,up,hr,ha,hlo,hrD,hrcube,hbounds⟩ :=
    shrink_ball_with_density_bounds c.open_source h0 hws.continuousOn hwpos
  refine ⟨{
    n := 3*d
    positive_n := ?_
    dimension := rfl
    a := a
    positive_a := ha
    radius := r
    positive_radius := hr
    closed_ball_in_cube := hrcube
    component := i
    center := p
    finite_stabilizer := H
    orthogonal := StabilizerLinearization.stabilizerOrthogonal F _ p
    extendedDomain := c.source
    open_extendedDomain := c.open_source
    closed_ball_in_extension := hrD
    invariant_extension := hsource
    coordinates := c
    coordinates_center := hp
    smooth_coordinates := hs
    coordinates_embedding := c.toPartialHomeomorph.isEmbedding_restrict
    coordinates_open := himage.symm ▸ c.open_target
    smooth_inverse := ⟨c.symm, himage.symm ▸ hi, fun x hx => c.left_inv hx⟩
    equivariance := heq
    separated := fun γ x y hx hy hxy => hsep γ _ (c.map_source hx) _ (c.map_source hy) hxy
    weight := w
    smooth_weight := hws
    invariant_weight := hwinv
    lower := lo
    upper := up
    positive_lower := hlo
    finite_bounds := hbounds
    coordinate_volume := ?_
  }, rfl, rfl⟩
  · have hd : 0 < d := KPCuspLogShape.dimension_pos F hF
    omega
  · have hb : Metric.ball (0 : E (3*d)) r ⊆ c.source :=
      fun x hx => hrD (subset_closure hx)
    have hh := hyperbolic_jacobian_three d Metric.isOpen_ball.measurableSet
      (fun x hx => ((hs x (hb hx)).differentiableWithinAt (by simp)).mono hb) (c.injOn.mono hb)
    convert hh using 1
    apply congrArg (Measure.map c)
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hx]

theorem normal_charts_cover (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) :
    ∀ x : X F ζ hζ U, ∃ C : Chart F ζ hζ hF U A,
      IsOpen (C.O F ζ hζ hF U) ∧ x ∈ C.O F ζ hζ hF U := by
  intro x
  obtain ⟨⟨i,q⟩,hqx⟩ := A.components.surjective x
  rw [A.components_formula] at hqx
  obtain ⟨p,rfl⟩ := Quotient.mk_surjective q
  obtain ⟨C,hCi,hCp⟩ := component_chart F ζ hζ hF U A i p
  refine ⟨C, chart_image_open F ζ hζ hF U A C, ?_⟩
  change x ∈ C.toBase F ζ hζ hF U '' Metric.ball 0 C.radius
  refine ⟨0,Metric.mem_ball_self C.positive_radius, ?_⟩
  change KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component)
    (KPCuspSiegel.projection F _ (C.coordinates 0)) = x
  rw [C.coordinates_center,hCp]
  subst i
  exact hqx

end DedekindZetaZeroFree.CoreChartLocalizers.CutoffConstruction

end
