module

public import DedekindZetaZeroFree.Metaplectic.Cubic.AdelicFiniteFactorClosure

@[expose] public section

noncomputable section
set_option maxRecDepth 4000
namespace DedekindZetaZeroFree.ActualFiniteFactor
open NumberField IsDedekindDomain KPAdelicCoverRestrictedProduct
open scoped NumberField Classical Topology
attribute [local instance] KPAdelicCoverRestrictedProduct.pglLocalTopology
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

structure FiniteCompactOpen where
  subgroup : OpenSubgroup (finiteSubgroup F ζ hζ)
  compact : IsCompact (subgroup : Set (finiteSubgroup F ζ hζ))

structure ProductLevelData where
  localLevel : ∀ q : HeightOneSpectrum (𝓞 F),
    CompactOpenLevel (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q))
  cofinally_standard : ∀ᶠ q in Filter.cofinite,
    (localLevel q).toOpenSubgroup.toSubgroup = pglCompact F ζ hζ (Sum.inr q)

def productTuples (J : ProductLevelData F ζ hζ) : Subgroup (RestrictedCover F ζ hζ) :=
  finiteTuples F ζ hζ ⊓ ⨅ q : HeightOneSpectrum (𝓞 F),
    ((J.localLevel q).toOpenSubgroup.toSubgroup).comap
      ((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
        (RestrictedProduct.evalMonoidHom (KPLocalCover.CubicGL2Raw F ζ hζ)
          (B := compact F ζ hζ) (Sum.inr q)))

def productSubgroup (J : ProductLevelData F ζ hζ) : Subgroup (Cover F ζ hζ) :=
  (productTuples F ζ hζ J).map
    ((scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ))

theorem productSubgroup_le_finite (J : ProductLevelData F ζ hζ) :
    productSubgroup F ζ hζ J ≤ finiteSubgroup F ζ hζ := by
  rw [finiteSubgroup_eq_tupleFactor]
  exact Subgroup.map_mono inf_le_left

 theorem sum_eventually {P : HeightOneSpectrum (𝓞 F) → Prop}
    (h : ∀ᶠ q in Filter.cofinite, P q) :
    ∀ᶠ v : KPHilbert.Place F in Filter.cofinite, (match v with | Sum.inl _ => True | Sum.inr q => P q) := by
  apply Filter.eventually_cofinite.mpr
  have hh := Filter.eventually_cofinite.mp h
  apply (hh.image (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F)).subset
  rintro (w | q) hw
  · simp at hw
  · exact ⟨q, hw, rfl⟩

 def levelTuple (J : ProductLevelData F ζ hζ)
    (x : ∀ q, (J.localLevel q).toOpenSubgroup) : RestrictedPGLCover F ζ hζ :=
  ⟨fun v => match v with | Sum.inl _ => 1 | Sum.inr q => (x q).val, by
    filter_upwards [sum_eventually F J.cofinally_standard] with v hv
    cases v with
    | inl w => exact Subgroup.one_mem _
    | inr q => rw [← hv]; exact (x q).property⟩

private theorem levelTuple_continuous (J : ProductLevelData F ζ hζ) :
    Continuous (levelTuple F ζ hζ J) := by
  let S : Set (KPHilbert.Place F) := {v | match v with
    | Sum.inl _ => True
    | Sum.inr q => (J.localLevel q).toOpenSubgroup.toSubgroup = pglCompact F ζ hζ (Sum.inr q)}
  have hS : Filter.cofinite ≤ Filter.principal S :=
    Filter.le_principal_iff.mpr (sum_eventually F J.cofinally_standard)
  let t (x : ∀ q, (J.localLevel q).toOpenSubgroup) :
      RestrictedProduct (fun v => KPPGLLocalCover.CubicPGL2 F ζ hζ v)
        (fun v => (pglCompact F ζ hζ v : Set _)) (Filter.principal S) :=
    ⟨(levelTuple F ζ hζ J x).val, Filter.eventually_principal.mpr (by
      intro v hv
      cases v with
      | inl w => exact Subgroup.one_mem _
      | inr q =>
        change (J.localLevel q).toOpenSubgroup.toSubgroup = pglCompact F ζ hζ (Sum.inr q) at hv
        change (x q).val ∈ pglCompact F ζ hζ (Sum.inr q)
        rw [← hv]; exact (x q).property)⟩
  have ht : Continuous t := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro v
    cases v with
    | inl w => exact continuous_const
    | inr q => exact continuous_subtype_val.comp (continuous_apply q)
  exact (RestrictedProduct.continuous_inclusion hS).comp ht

private theorem levelTuple_lift (J : ProductLevelData F ζ hζ)
    (x : ∀ q, (J.localLevel q).toOpenSubgroup) :
    ∃ y ∈ productTuples F ζ hζ J,
      restrictedPGLQuotient F ζ hζ y = levelTuple F ζ hζ J x := by
  have hlift (q : HeightOneSpectrum (𝓞 F)) :
      ∃ g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q),
        KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g = (x q).val ∧
        ((x q).val ∈ pglCompact F ζ hζ (Sum.inr q) → g ∈ compact F ζ hζ (Sum.inr q)) := by
    by_cases hx : (x q).val ∈ pglCompact F ζ hζ (Sum.inr q)
    · obtain ⟨g, hg, he⟩ := hx
      exact ⟨g, he, fun _ => hg⟩
    · obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
        (KPPGLLocalCover.splitScalarSubgroup F ζ hζ (Sum.inr q)) (x q).val
      exact ⟨g, hg, fun h => (hx h).elim⟩
  choose g hg hcompact using hlift
  let y : RestrictedCover F ζ hζ := ⟨fun v => match v with | Sum.inl _ => 1 | Sum.inr q => g q, by
    filter_upwards [sum_eventually F J.cofinally_standard] with v hv
    cases v with
    | inl w => exact Subgroup.one_mem _
    | inr q => exact hcompact q (by rw [← hv]; exact (x q).property)⟩
  refine ⟨y, ?_, ?_⟩
  · constructor
    · intro w; rfl
    · apply Subgroup.mem_iInf.mpr
      intro q
      change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (g q) ∈ (J.localLevel q).toOpenSubgroup
      rw [hg]
      exact (x q).property
  · ext v
    cases v with
    | inl w => change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w) 1 = 1; exact map_one _
    | inr q => exact hg q

private theorem compact_half (J : ProductLevelData F ζ hζ) :
    IsCompact ((productSubgroup F ζ hζ J).comap
      (finiteSubgroup F ζ hζ).subtype : Set (finiteSubgroup F ζ hζ)) := by
  obtain ⟨e, he, hei, herule⟩ := scalar_quotient_commutes_with_amalgamation F ζ hζ
  let f : (∀ q, (J.localLevel q).toOpenSubgroup) → Cover F ζ hζ :=
    fun x => e.symm (QuotientGroup.mk' (pglM F ζ hζ) (levelTuple F ζ hζ J x))
  have hf : Continuous f := hei.comp (QuotientGroup.continuous_mk.comp (levelTuple_continuous F ζ hζ J))
  have hmem (x : ∀ q, (J.localLevel q).toOpenSubgroup) : f x ∈ productSubgroup F ζ hζ J := by
    obtain ⟨y, hy, hye⟩ := levelTuple_lift F ζ hζ J x
    refine ⟨y, hy, ?_⟩
    apply e.injective
    change e (scalarQuotient F ζ hζ (amalgamation F ζ hζ y)) = e (e.symm _)
    rw [herule, hye, e.apply_symm_apply]
  let ff : (∀ q, (J.localLevel q).toOpenSubgroup) → finiteSubgroup F ζ hζ :=
    fun x => ⟨f x, productSubgroup_le_finite F ζ hζ J (hmem x)⟩
  have hff : Continuous ff := hf.subtype_mk _
  letI : ∀ q, CompactSpace (J.localLevel q).toOpenSubgroup := fun q =>
    isCompact_iff_compactSpace.mp (J.localLevel q).isCompact
  have hsurj : Set.range ff = ((productSubgroup F ζ hζ J).comap
      (finiteSubgroup F ζ hζ).subtype : Set (finiteSubgroup F ζ hζ)) := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩; exact hmem x
    · rintro ⟨y, hy, hye⟩
      have hq : ∀ q, KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (y (Sum.inr q)) ∈
          (J.localLevel q).toOpenSubgroup := by
        exact fun q => (Subgroup.mem_iInf.mp hy.2 q)
      let x : ∀ q, (J.localLevel q).toOpenSubgroup := fun q => ⟨_, hq q⟩
      refine ⟨x, Subtype.ext ?_⟩
      change f x = u.val
      change scalarQuotient F ζ hζ (amalgamation F ζ hζ y) = u.val at hye
      rw [← hye]
      apply e.injective
      change e (e.symm _) = e (scalarQuotient F ζ hζ (amalgamation F ζ hζ y))
      rw [herule, e.apply_symm_apply]
      congr 1
      ext v
      cases v with
      | inl w => change 1 = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w) (y (Sum.inl w)); rw [hy.1 w, map_one]
      | inr q => rfl
  rw [← hsurj]
  exact isCompact_range hff

private theorem restricted_forall_open {ι : Type*} {R : ι → Type*}
    [∀ i, TopologicalSpace (R i)] (B U : ∀ i, Set (R i))
    (hU : ∀ i, IsOpen (U i)) (hBU : ∀ᶠ i in Filter.cofinite, B i ⊆ U i) :
    IsOpen {x : RestrictedProduct R B Filter.cofinite | ∀ i, x i ∈ U i} := by
  simp_rw +instances [RestrictedProduct.topologicalSpace_eq_iSup Filter.cofinite,
    isOpen_iSup_iff, isOpen_coinduced]
  intro S hS
  let T : Set ι := Sᶜ ∪ {i | ¬ B i ⊆ U i}
  have hT : T.Finite :=
    (Filter.eventually_cofinite.mp (Filter.le_principal_iff.mp hS)).union
      (Filter.eventually_cofinite.mp hBU)
  have heq : {x : RestrictedProduct R B (Filter.principal S) | ∀ i, x i ∈ U i} =
      (fun x : RestrictedProduct R B (Filter.principal S) => x.val) ⁻¹' Set.pi T U := by
    ext x
    constructor
    · intro hx i hi; exact hx i
    · intro hx i
      by_cases hi : i ∈ T
      · exact hx i hi
      · have hiS : i ∈ S := by
          by_contra h
          exact hi (Or.inl h)
        have hiB : B i ⊆ U i := by
          exact not_not.mp (fun h => hi (Or.inr h))
        exact hiB (Filter.eventually_principal.mp x.property i hiS)
  change IsOpen {x : RestrictedProduct R B (Filter.principal S) | ∀ i, x i ∈ U i}
  rw [heq]
  exact (isOpen_set_pi hT (fun i _ => hU i)).preimage RestrictedProduct.continuous_coe

 instance raw_group (v : KPHilbert.Place F) :
    IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ v) := by
  cases v with
  | inl w => exact (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.1
  | inr q => exact (KPLocalChartTopology.finite_topological_group F ζ hζ q _
      (depth_admissible F ζ hζ q)).2.2

private theorem raw_open (J : ProductLevelData F ζ hζ) :
    IsOpen {x : RestrictedCover F ζ hζ |
      (∀ w : InfinitePlace F, (x (Sum.inl w)).epsilon = 1) ∧
      (∀ q : HeightOneSpectrum (𝓞 F), KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (x (Sum.inr q)) ∈ (J.localLevel q).toOpenSubgroup)} := by
  let U : ∀ v : KPHilbert.Place F, Set (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
    fun v => match v with
    | Sum.inl w => {g | g.epsilon = 1}
    | Sum.inr q => KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) ⁻¹' (J.localLevel q).toOpenSubgroup
  have hU : ∀ v, IsOpen (U v) := by
    intro v
    cases v with
    | inl w =>
      letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
      letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
      have hc : Continuous (KPLocalChartTopology.complexCoordinates F ζ hζ w) := continuous_induced_dom
      exact isOpen_discrete ({1} : Set (rootsOfUnity 3 F)) |>.preimage (continuous_snd.comp hc)
    | inr q => exact (J.localLevel q).toOpenSubgroup.isOpen.preimage QuotientGroup.continuous_mk
  have hBU : ∀ᶠ v in Filter.cofinite, (compact F ζ hζ v : Set _) ⊆ U v := by
    have hq : ∀ᶠ q in Filter.cofinite, (compact F ζ hζ (Sum.inr q) : Set _) ⊆ U (Sum.inr q) := by
      filter_upwards [J.cofinally_standard] with q hq
      intro g hg
      change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g ∈ (J.localLevel q).toOpenSubgroup
      change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g ∈ (J.localLevel q).toOpenSubgroup.toSubgroup
      rw [hq]
      exact ⟨g, hg, rfl⟩
    apply Filter.eventually_cofinite.mpr
    have hh := Filter.eventually_cofinite.mp hq
    apply ((Set.finite_range (Sum.inl : InfinitePlace F → KPHilbert.Place F)).union
      (hh.image (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F))).subset
    rintro (w | q) hw
    · exact Or.inl ⟨w, rfl⟩
    · exact Or.inr ⟨q, hw, rfl⟩
  have ho := restricted_forall_open (fun v => (compact F ζ hζ v : Set _)) U hU hBU
  convert ho using 1
  ext x
  constructor
  · rintro ⟨hw, hq⟩ (w | q); exact hw w; exact hq q
  · intro hx; exact ⟨fun w => hx (Sum.inl w), fun q => hx (Sum.inr q)⟩

private theorem remove_arch (J : ProductLevelData F ζ hζ) (x : RestrictedCover F ζ hζ)
    (hx : scalarQuotient F ζ hζ (amalgamation F ζ hζ x) ∈ finiteSubgroup F ζ hζ)
    (heps : ∀ w : InfinitePlace F, (x (Sum.inl w)).epsilon = 1)
    (hlevel : ∀ q : HeightOneSpectrum (𝓞 F), KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (x (Sum.inr q)) ∈ (J.localLevel q).toOpenSubgroup) :
    scalarQuotient F ζ hζ (amalgamation F ζ hζ x) ∈ productSubgroup F ζ hζ J := by
  rw [finiteSubgroup_eq_ker] at hx
  have hs : ∀ w : InfinitePlace F, ∃ u : w.Completionˣ,
      (x (Sum.inl w)).g = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    intro w
    have hw := congrFun hx w
    rw [PGLComplex.AdelicSlicesRaw.archProjection_restricted_eval] at hw
    change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _ (x (Sum.inl w)).g) = 1 at hw
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hw
    obtain ⟨u, hu⟩ := hw
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ w)
    refine ⟨Units.map e.symm.toRingHom u, ?_⟩
    change Matrix.GeneralLinearGroup.scalar (Fin 2) u =
      Matrix.GeneralLinearGroup.map e.toRingHom (x (Sum.inl w)).g at hu
    have he := congrArg (Matrix.GeneralLinearGroup.map e.symm.toRingHom) hu
    rw [Matrix.GeneralLinearGroup.map_scalar] at he
    have hi : Matrix.GeneralLinearGroup.map e.symm.toRingHom
        (Matrix.GeneralLinearGroup.map e.toRingHom (x (Sum.inl w)).g) = (x (Sum.inl w)).g := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      simp [Matrix.GeneralLinearGroup.map_apply]
    rw [hi] at he
    exact he.symm
  choose s hs using hs
  let z : Ideles F :=
    ⟨(fun w => (s w).val, 1), (fun w => (s w).inv, 1),
      by apply Prod.ext; funext w; exact (s w).val_inv; exact one_mul _,
      by apply Prod.ext; funext w; exact (s w).inv_val; exact one_mul _⟩
  have hz (w : InfinitePlace F) : Units.map (adeleEval F (Sum.inl w)) z = s w := by
    apply Units.ext; rfl
  have hzf (q : HeightOneSpectrum (𝓞 F)) : Units.map (adeleEval F (Sum.inr q)).toMonoidHom z = 1 := by
    apply Units.ext; rfl
  let y := x * (scalarTuple F ζ hζ z)⁻¹
  have hy (w : InfinitePlace F) : y (Sum.inl w) = 1 := by
    have hscalar : scalarCoordinates F ζ hζ z (Sum.inl w) = x (Sum.inl w) := by
      change KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w) (Units.map (adeleEval F (Sum.inl w)) z) = _
      rw [hz]
      have hg : (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w) (s w)).g =
          (x (Sum.inl w)).g := (hs w).symm
      have hep : (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w) (s w)).epsilon =
          (x (Sum.inl w)).epsilon := (heps w).symm
      cases h : x (Sum.inl w)
      simp only [h] at hg hep ⊢
      cases hg
      cases hep
      rfl
    change x (Sum.inl w) * (scalarCoordinates F ζ hζ z (Sum.inl w))⁻¹ = 1
    rw [hscalar, mul_inv_cancel]
  have hyf (q : HeightOneSpectrum (𝓞 F)) : y (Sum.inr q) = x (Sum.inr q) := by
    change x (Sum.inr q) * (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) (Units.map (adeleEval F (Sum.inr q)).toMonoidHom z))⁻¹ = _
    rw [hzf, map_one, inv_one, mul_one]
  refine ⟨y, ⟨hy, Subgroup.mem_iInf.mpr (fun q => ?_)⟩, ?_⟩
  · change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (y (Sum.inr q)) ∈ (J.localLevel q).toOpenSubgroup
    rw [hyf]; exact hlevel q
  · change scalarQuotient F ζ hζ (amalgamation F ζ hζ (x * (scalarTuple F ζ hζ z)⁻¹)) = _
    rw [map_mul, map_inv, map_mul, map_inv]
    have hscalar : scalarQuotient F ζ hζ (scalarHom F ζ hζ z) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨z, rfl⟩
    change scalarQuotient F ζ hζ (amalgamation F ζ hζ x) *
      (scalarQuotient F ζ hζ (scalarHom F ζ hζ z))⁻¹ = _
    rw [hscalar, inv_one, mul_one]
private theorem open_half (J : ProductLevelData F ζ hζ) :
    IsOpen ((productSubgroup F ζ hζ J).comap
      (finiteSubgroup F ζ hζ).subtype : Set (finiteSubgroup F ζ hζ)) := by
  letI : Fact (∀ v : KPHilbert.Place F, IsOpen (compact F ζ hζ v : Set (KPLocalCover.CubicGL2Raw F ζ hζ v))) := ⟨fun v => compact_open F ζ hζ v⟩
  let A : Set (RestrictedCover F ζ hζ) := {x |
      (∀ w : InfinitePlace F, (x (Sum.inl w)).epsilon = 1) ∧
      (∀ q : HeightOneSpectrum (𝓞 F), KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (x (Sum.inr q)) ∈ (J.localLevel q).toOpenSubgroup)}
  let q := (scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ)
  have ho : IsOpen (q '' A) :=
    (QuotientGroup.isOpenMap_coe.comp QuotientGroup.isOpenMap_coe) _ (raw_open F ζ hζ J)
  have he : ((productSubgroup F ζ hζ J).comap
      (finiteSubgroup F ζ hζ).subtype : Set (finiteSubgroup F ζ hζ)) =
      Subtype.val ⁻¹' (q '' A) := by
    ext u
    constructor
    · rintro ⟨x, hx, hxu⟩
      refine ⟨x, ⟨?_, fun v => Subgroup.mem_iInf.mp hx.2 v⟩, hxu⟩
      intro w
      rw [hx.1 w]
      rfl
    · rintro ⟨x, ⟨hxe, hxl⟩, hxu⟩
      change q x = u.val at hxu
      change u.val ∈ productSubgroup F ζ hζ J
      rw [← hxu]
      apply remove_arch F ζ hζ J x _ hxe hxl
      change q x ∈ finiteSubgroup F ζ hζ
      rw [hxu]
      exact u.property
  rw [he]
  exact ho.preimage continuous_subtype_val

theorem productSubgroup_compact_open (J : ProductLevelData F ζ hζ) :
    IsCompact ((productSubgroup F ζ hζ J).comap
      (finiteSubgroup F ζ hζ).subtype : Set (finiteSubgroup F ζ hζ)) ∧
    IsOpen ((productSubgroup F ζ hζ J).comap
      (finiteSubgroup F ζ hζ).subtype : Set (finiteSubgroup F ζ hζ)) := by
  exact ⟨compact_half F ζ hζ J, open_half F ζ hζ J⟩

private theorem pgl_standard (q : HeightOneSpectrum (𝓞 F)) :
    IsCompact (pglCompact F ζ hζ (Sum.inr q) : Set (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q))) ∧
      IsOpen (pglCompact F ζ hζ (Sum.inr q) : Set (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q))) := by
  letI := KPAdelicCoverRestrictedProduct.localTopology F ζ hζ (Sum.inr q)
  letI : IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :=
    (KPLocalChartTopology.finite_topological_group F ζ hζ q _
      (depth_admissible F ζ hζ q)).2.2
  change IsCompact ((finiteCompact F ζ hζ q).map
    (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)) : Set (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q))) ∧ _
  exact ⟨(finiteCompact_compact_open F ζ hζ q).1.image QuotientGroup.continuous_mk,
    QuotientGroup.isOpenMap_coe _ (finiteCompact_compact_open F ζ hζ q).2⟩

theorem pgl_standard_compact_open (q : HeightOneSpectrum (𝓞 F)) :
    IsCompact (pglCompact F ζ hζ (Sum.inr q) : Set (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q))) ∧
      IsOpen (pglCompact F ζ hζ (Sum.inr q) : Set (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q))) :=
  pgl_standard F ζ hζ q

private theorem local_basis (q : HeightOneSpectrum (𝓞 F))
    (U : Set (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q))) (hU : U ∈ 𝓝 1) :
    ∃ L : CompactOpenLevel (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)),
      (L.toOpenSubgroup : Set _) ⊆ U := by
  let m := depth F ζ hζ q
  have hm := depth_admissible F ζ hζ q
  letI := KPLocalChartTopology.translatedTopology F ζ hζ q m
  letI := (KPLocalChartTopology.finite_topological_group F ζ hζ q m hm).2.2
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ q m hm).2.2.1
  obtain ⟨s, hs, hi, _⟩ := KPDeepRawSplitting.raw_section_splitting F ζ hζ q m
    (fun g hg h hh => KPDeepRawSplitting.sigmaTwo_eq_one_on_Gamma F ζ hζ q m hm.2 g h hg hh)
  have he : (s : KPLocalCube.Gamma F q m →
      KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) =
      KPLocalChartTopology.translatedChart F ζ hζ q m 1 := by
    funext k
    simp [KPLocalChartTopology.translatedChart, hs]
  have hsopen : Topology.IsOpenEmbedding s := by
    rw [he]
    exact KPLocalChartTopology.translatedChart_isOpenEmbedding F ζ hζ q m hm 1
  let Q := KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
  have hQ : Continuous Q := QuotientGroup.continuous_mk
  have hQo : IsOpenMap Q := QuotientGroup.isOpenMap_coe
  have hn : (fun k => Q (s k)) ⁻¹' U ∈ nhds (1 : KPLocalCube.Gamma F q m) := by
    exact (hQ.comp hsopen.continuous).continuousAt.preimage_mem_nhds (by simpa using hU)
  rw [nhds_subtype] at hn
  obtain ⟨r, hr, hsub⟩ :=
    ((KPLocalCube.Gamma_nhds_basis F q m hm.1).comap Subtype.val).mem_iff.mp hn
  let J := (KPLocalCube.Gamma F q r).subgroupOf (KPLocalCube.Gamma F q m)
  have hJo : IsOpen (J : Set (KPLocalCube.Gamma F q m)) :=
    (KPLocalCube.Gamma_compact_open F q r (hm.1.trans hr)).2.preimage continuous_subtype_val
  letI : CompactSpace (KPLocalCube.Gamma F q m) :=
    isCompact_iff_compactSpace.mp (KPLocalCube.Gamma_compact_open F q m hm.1).1
  have hJc : IsCompact (J : Set (KPLocalCube.Gamma F q m)) :=
    isCompact_univ.of_isClosed_subset
      (show IsClosed (J : Set (KPLocalCube.Gamma F q m)) from
        (show OpenSubgroup (KPLocalCube.Gamma F q m) from ⟨J, hJo⟩).isClosed)
      (Set.subset_univ _)
  let L := J.map (Q.comp s)
  have hLo : IsOpen (L : Set (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q))) := by
    rw [Subgroup.coe_map]
    exact (hQo.comp hsopen.isOpenMap) _ hJo
  have hLc : IsCompact (L : Set (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q))) := by
    rw [Subgroup.coe_map]
    exact hJc.image (hQ.comp hsopen.continuous)
  refine ⟨⟨⟨L, hLo⟩, hLc⟩, ?_⟩
  rintro x ⟨k, hk, rfl⟩
  exact hsub hk

theorem productLevels_cofinal (W : Set (finiteSubgroup F ζ hζ)) (hW : W ∈ 𝓝 1) :
    ∃ J : ProductLevelData F ζ hζ,
      ((productSubgroup F ζ hζ J).comap (finiteSubgroup F ζ hζ).subtype :
        Set (finiteSubgroup F ζ hζ)) ⊆ W := by
  let J0 : ProductLevelData F ζ hζ :=
    ⟨fun q => ⟨⟨pglCompact F ζ hζ (Sum.inr q), (pgl_standard F ζ hζ q).2⟩,
      (pgl_standard F ζ hζ q).1⟩, Filter.Eventually.of_forall fun _ => rfl⟩
  obtain ⟨e, he, hei, herule⟩ := scalar_quotient_commutes_with_amalgamation F ζ hζ
  let f : (∀ q, (J0.localLevel q).toOpenSubgroup) → Cover F ζ hζ :=
    fun x => e.symm (QuotientGroup.mk' (pglM F ζ hζ) (levelTuple F ζ hζ J0 x))
  have hf : Continuous f := hei.comp (QuotientGroup.continuous_mk.comp (levelTuple_continuous F ζ hζ J0))
  have hmem (x : ∀ q, (J0.localLevel q).toOpenSubgroup) : f x ∈ productSubgroup F ζ hζ J0 := by
    obtain ⟨y, hy, hye⟩ := levelTuple_lift F ζ hζ J0 x
    refine ⟨y, hy, ?_⟩
    apply e.injective
    change e (scalarQuotient F ζ hζ (amalgamation F ζ hζ y)) = e (e.symm _)
    rw [herule, hye, e.apply_symm_apply]
  let ff : (∀ q, (J0.localLevel q).toOpenSubgroup) → finiteSubgroup F ζ hζ :=
    fun x => ⟨f x, productSubgroup_le_finite F ζ hζ J0 (hmem x)⟩
  have hff : Continuous ff := hf.subtype_mk _
  have h1 : ff 1 = 1 := by
    apply Subtype.ext
    change e.symm (QuotientGroup.mk' (pglM F ζ hζ) (levelTuple F ζ hζ J0 1)) = 1
    have ht : levelTuple F ζ hζ J0 1 = 1 := by
      ext v; cases v <;> rfl
    rw [ht, map_one, map_one]
  have hpre : ff ⁻¹' W ∈ 𝓝 1 := hff.continuousAt.preimage_mem_nhds (by simpa only [h1] using hW)
  rw [nhds_pi] at hpre
  obtain ⟨s, t, ht, hsub⟩ := Filter.mem_pi'.mp hpre
  have hl (q : HeightOneSpectrum (𝓞 F)) :
      ∃ L : CompactOpenLevel (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)),
        (L.toOpenSubgroup : Set (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q))) ⊆
          (pglCompact F ζ hζ (Sum.inr q) : Set (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q))) ∧
        ∀ g : (J0.localLevel q).toOpenSubgroup, g.val ∈ L.toOpenSubgroup → g ∈ t q := by
    obtain ⟨V, hV, hVs⟩ := (mem_nhds_subtype _ _ _).mp (ht q)
    have hn : V ∩ (pglCompact F ζ hζ (Sum.inr q) : Set _) ∈ 𝓝 1 :=
      Filter.inter_mem hV ((pgl_standard F ζ hζ q).2.mem_nhds (Subgroup.one_mem _))
    obtain ⟨L, hL⟩ := local_basis F ζ hζ q _ hn
    refine ⟨L, fun g hg => (hL hg).2, ?_⟩
    intro g hg
    exact hVs ((hL hg).1)
  choose L hL htL using hl
  let J : ProductLevelData F ζ hζ :=
    ⟨fun q => if q ∈ s then L q else J0.localLevel q, by
      filter_upwards [s.finite_toSet.compl_mem_cofinite] with q hq
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hq
      simp [hq, J0]⟩
  refine ⟨J, ?_⟩
  intro u hu
  obtain ⟨y, hy, hye⟩ := hu
  have hq : ∀ q, KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (y (Sum.inr q)) ∈
      (J.localLevel q).toOpenSubgroup := fun q => Subgroup.mem_iInf.mp hy.2 q
  have hstd (q : HeightOneSpectrum (𝓞 F)) :
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (y (Sum.inr q)) ∈
        (J0.localLevel q).toOpenSubgroup := by
    have h := hq q
    by_cases hs : q ∈ s
    · change _ ∈ (if q ∈ s then L q else J0.localLevel q).toOpenSubgroup at h
      rw [if_pos hs] at h
      exact hL q h
    · simpa only [J, if_neg hs] using h
  let x : ∀ q, (J0.localLevel q).toOpenSubgroup := fun q => ⟨_, hstd q⟩
  have hxu : ff x = u := by
    apply Subtype.ext
    change f x = u.val
    change scalarQuotient F ζ hζ (amalgamation F ζ hζ y) = u.val at hye
    rw [← hye]
    apply e.injective
    change e (e.symm _) = e (scalarQuotient F ζ hζ (amalgamation F ζ hζ y))
    rw [herule, e.apply_symm_apply]
    congr 1
    ext v
    cases v with
    | inl w => change 1 = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w) (y (Sum.inl w)); rw [hy.1 w, map_one]
    | inr q => rfl
  rw [← hxu]
  apply hsub
  intro q hqs
  apply htL q (x q)
  have h := hq q
  change _ ∈ (if q ∈ s then L q else J0.localLevel q).toOpenSubgroup at h
  rwa [if_pos (Finset.mem_coe.mp hqs)] at h

def productLevel (J : ProductLevelData F ζ hζ) : FiniteCompactOpen F ζ hζ :=
  ⟨⟨(productSubgroup F ζ hζ J).comap (finiteSubgroup F ζ hζ).subtype,
      (productSubgroup_compact_open F ζ hζ J).2⟩,
    (productSubgroup_compact_open F ζ hζ J).1⟩

theorem finiteSubgroup_normal : (finiteSubgroup F ζ hζ).Normal := by
  rw [finiteSubgroup_eq_ker]
  infer_instance

end DedekindZetaZeroFree.ActualFiniteFactor

end

section

noncomputable section
set_option maxRecDepth 4000
namespace DedekindZetaZeroFree.ActualFiniteFactor
open NumberField IsDedekindDomain KPAdelicCoverRestrictedProduct
open scoped NumberField Classical Topology
attribute [local instance] KPAdelicCoverRestrictedProduct.pglLocalTopology
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem productLevel_rule (J : ProductLevelData F ζ hζ) (u : finiteSubgroup F ζ hζ) :
    u ∈ (productLevel F ζ hζ J).subgroup ↔
      ∃ x : RestrictedCover F ζ hζ,
        (∀ w : InfinitePlace F, x (Sum.inl w) = 1) ∧
        (∀ q : HeightOneSpectrum (𝓞 F),
          KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (x (Sum.inr q)) ∈
            (J.localLevel q).toOpenSubgroup) ∧
        scalarQuotient F ζ hζ (amalgamation F ζ hζ x) = u.val := by
  change u.val ∈ productSubgroup F ζ hζ J ↔ _
  simp only [productSubgroup, Subgroup.mem_map, productTuples, Subgroup.mem_inf,
    Subgroup.mem_iInf, Subgroup.mem_comap]
  constructor
  · rintro ⟨x, ⟨hx, hq⟩, he⟩
    exact ⟨x, hx, hq, he⟩
  · rintro ⟨x, hx, hq, he⟩
    exact ⟨x, ⟨hx, hq⟩, he⟩

end DedekindZetaZeroFree.ActualFiniteFactor

end
end
