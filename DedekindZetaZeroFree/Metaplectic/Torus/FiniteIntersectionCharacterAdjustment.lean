module

public import DedekindZetaZeroFree.Metaplectic.Torus.ProductPolarizationCoordinates

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ProductPolarization
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology localCoverTopology

namespace FiniteAdjustmentSupport

private theorem single_cont (v : KPHilbert.Place F) : Continuous (RestrictedProduct.mulSingle (KPGlobalCubicIdelePairing.U F) v) := by
  let S : Set (KPHilbert.Place F) := {v}ᶜ
  let t : LocalD F v → RestrictedProduct (LocalD F) (fun w => (KPGlobalCubicIdelePairing.U F w : Set (LocalD F w))) (Filter.principal S) :=
    fun l => ⟨Pi.mulSingle v l, by intro w hw; simp only [S, Set.mem_compl_iff, Set.mem_singleton_iff] at hw; simp [Pi.mulSingle_eq_of_ne hw, Subgroup.one_mem]⟩
  have ht : Continuous t := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro w
    change Continuous (fun l : LocalD F v => Pi.mulSingle v l w)
    by_cases hw : w = v
    · subst w
      simp only [Pi.mulSingle_eq_same]
      exact continuous_id
    · simpa only [Pi.mulSingle_eq_of_ne hw] using (continuous_const : Continuous (fun _ : LocalD F v => (1 : LocalD F w)))
  have hS : Filter.cofinite ≤ Filter.principal S := by simp [S]
  exact (RestrictedProduct.continuous_inclusion hS).comp ht
theorem local_finite (v : KPHilbert.Place F) : Finite (LocalD F v) := by
  cases v with
  | inl w => letI := KPGlobalCubicIdelePairing.local_complex_trivial F w; infer_instance
  | inr q =>
    letI : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
    letI : IsNonarchimedeanLocalField (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
    exact ClassFieldTheory.powerClassGroup_finite _ 3 (by norm_num)
theorem local_discrete (v : KPHilbert.Place F) : DiscreteTopology (LocalD F v) := by
  obtain ⟨e, he⟩ := KPGlobalCubicIdelePairing.restricted_cube_quotient F
  letI := KPGlobalCubicIdelePairing.hausdorff F
  letI : T2Space (KPGlobalCubicIdelePairing.RestrictedClasses F) := e.toHomeomorph.symm.isEmbedding.t2Space
  letI : T2Space (LocalD F v) := T2Space.of_injective_continuous
    (RestrictedProduct.mulSingle_injective (KPGlobalCubicIdelePairing.U F) v) (single_cont F v)
  letI := local_finite F v
  infer_instance
private theorem eventually_eq (P : CompatibleLocalData F ζ hζ) :
    ∀ᶠ v in Filter.cofinite, (P.localData v).L = KPGlobalCubicIdelePairing.U F v := by
  have hf := Filter.eventually_cofinite.mp P.unramified_almost_everywhere
  filter_upwards [(hf.image (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F)).compl_mem_cofinite] with v hv
  cases v with
  | inl w => exact P.complex_full w
  | inr q =>
    have hu : IsUnramified F ζ hζ q (P.localData (Sum.inr q)) := by
      by_contra h
      exact hv ⟨q, h, rfl⟩
    exact hu.2.1
private theorem restrictedM_compact_open (P : CompatibleLocalData F ζ hζ) :
    IsCompact (restrictedM F ζ hζ P : Set (KPGlobalCubicIdelePairing.RestrictedClasses F)) ∧
    IsOpen (restrictedM F ζ hζ P : Set (KPGlobalCubicIdelePairing.RestrictedClasses F)) := by
  letI : ∀ v, Finite (LocalD F v) := local_finite F
  letI : ∀ v, DiscreteTopology (LocalD F v) := local_discrete F
  let L := fun v => ((P.localData v).L : Set (LocalD F v))
  let U := fun v => (KPGlobalCubicIdelePairing.U F v : Set (LocalD F v))
  have hLU : ∀ᶠ v in Filter.cofinite, L v ⊆ U v := by
    filter_upwards [eventually_eq F ζ hζ P] with v hv
    change ((P.localData v).L : Set (LocalD F v)) ⊆ (KPGlobalCubicIdelePairing.U F v : Set (LocalD F v))
    rw [hv]
  have hUL : ∀ᶠ v in Filter.cofinite, U v ⊆ L v := by
    filter_upwards [eventually_eq F ζ hζ P] with v hv
    change (KPGlobalCubicIdelePairing.U F v : Set (LocalD F v)) ⊆ ((P.localData v).L : Set (LocalD F v))
    rw [hv]
  let f : RestrictedProduct (LocalD F) L Filter.cofinite → KPGlobalCubicIdelePairing.RestrictedClasses F :=
    RestrictedProduct.mapAlong (LocalD F) (LocalD F) id Filter.tendsto_id (fun _ => id) hLU
  let g : KPGlobalCubicIdelePairing.RestrictedClasses F → RestrictedProduct (LocalD F) L Filter.cofinite :=
    RestrictedProduct.mapAlong (LocalD F) (LocalD F) id Filter.tendsto_id (fun _ => id) hUL
  have hf : Continuous f := RestrictedProduct.mapAlong_continuous _ _ _ _ _ _ (fun _ => continuous_id)
  have hg : Continuous g := RestrictedProduct.mapAlong_continuous _ _ _ _ _ _ (fun _ => continuous_id)
  let t : (∀ v, (P.localData v).L) → RestrictedProduct (LocalD F) L Filter.cofinite :=
    RestrictedProduct.structureMap _ L Filter.cofinite
  have ht : Continuous t :=
    (RestrictedProduct.isOpenEmbedding_structureMap (fun v => isOpen_discrete (L v))).continuous
  have hrange : Set.range (f ∘ t) = (restrictedM F ζ hζ P : Set (KPGlobalCubicIdelePairing.RestrictedClasses F)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact fun v => (y v).property
    · intro hx
      exact ⟨fun v => ⟨x v, hx v⟩, by ext v; rfl⟩
  have hcomp : IsCompact (restrictedM F ζ hζ P : Set (KPGlobalCubicIdelePairing.RestrictedClasses F)) := by
    rw [← hrange]
    exact isCompact_range (hf.comp ht)
  refine ⟨hcomp, ?_⟩
  exact (RestrictedProduct.isOpen_forall_mem (fun v => isOpen_discrete (L v))).preimage hg

theorem M_compact_open (P : CompatibleLocalData F ζ hζ) :
    IsCompact (M F ζ hζ P : Set (D F)) ∧ IsOpen (M F ζ hζ P : Set (D F)) := by
  obtain ⟨e, he⟩ := KPGlobalCubicIdelePairing.restricted_cube_quotient F
  have hset : (M F ζ hζ P : Set (D F)) =
      e ⁻¹' (restrictedM F ζ hζ P : Set (KPGlobalCubicIdelePairing.RestrictedClasses F)) := by
    ext x
    change KPGlobalCubicIdelePairing.classComparison F x ∈ restrictedM F ζ hζ P ↔
      e x ∈ restrictedM F ζ hζ P
    rw [he]
  rw [hset]
  exact ⟨e.toHomeomorph.isCompact_preimage.mpr (restrictedM_compact_open F ζ hζ P).1,
    (restrictedM_compact_open F ζ hζ P).2.preimage e.continuous⟩

theorem J_finite (P : CompatibleLocalData F ζ hζ) : Finite (J F ζ hζ P) := by
  letI := KPGlobalCubicIdelePairing.hausdorff F
  letI := KPGlobalPrincipalCubicLagrangian.principal_discrete F ζ hζ
  have hA : IsClosed (KPGlobalPrincipalCubicLagrangian.A F : Set (D F)) :=
    Subgroup.isClosed_of_discreteTopology
  have hJ : IsCompact (J F ζ hζ P : Set (D F)) :=
    ((M_compact_open F ζ hζ P).1.inter_left hA)
  have hd : IsDiscrete (J F ζ hζ P : Set (D F)) :=
    (show IsDiscrete (KPGlobalPrincipalCubicLagrangian.A F : Set (D F)) from
      isDiscrete_iff_discreteTopology.mpr inferInstance).mono inf_le_left
  exact (hJ.finite hd).to_subtype

theorem exists_finite_coordinate_injection (P : CompatibleLocalData F ζ hζ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      Function.Injective (fun j : J F ζ hζ P =>
        fun q : S => KPGlobalCubicIdelePairing.classComparison F j.val (Sum.inr q.val)) := by
  classical
  letI := J_finite F ζ hζ P
  obtain ⟨e, he⟩ := KPGlobalCubicIdelePairing.restricted_cube_quotient F
  have hsep (x y : J F ζ hζ P) (hne : x ≠ y) :
      ∃ q : HeightOneSpectrum (𝓞 F),
        KPGlobalCubicIdelePairing.classComparison F x.val (Sum.inr q) ≠
          KPGlobalCubicIdelePairing.classComparison F y.val (Sum.inr q) := by
    by_contra! h
    apply hne
    apply Subtype.ext
    apply e.injective
    rw [he, he]
    ext v
    cases v with
    | inl w =>
      letI := KPGlobalCubicIdelePairing.local_complex_trivial F w
      exact Subsingleton.elim _ _
    | inr q => exact h q
  let T := {p : J F ζ hζ P × J F ζ hζ P // p.1 ≠ p.2}
  let f : T → HeightOneSpectrum (𝓞 F) := fun p => Classical.choose (hsep p.val.1 p.val.2 p.property)
  have hf (p : T) := Classical.choose_spec (hsep p.val.1 p.val.2 p.property)
  let S := (Set.finite_range f).toFinset
  refine ⟨S, ?_⟩
  intro x y hxy
  by_contra hne
  let p : T := ⟨(x, y), hne⟩
  have hmem : f p ∈ S := by simp only [S, Set.Finite.mem_toFinset]; exact ⟨p, rfl⟩
  exact hf p (congrFun hxy ⟨f p, hmem⟩)

theorem adjustedLocalValue_outside (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ T.S)
    (b : localPreimage F ζ hζ (Sum.inr q) (P.localData (Sum.inr q)).L) :
    adjustedLocalValue F ζ hζ P T (Sum.inr q) b = (P.localData (Sum.inr q)).lambda b := by
  simp [adjustedLocalValue, T.outside_unchanged q hq]

private theorem rawCoordinate_val (P : CompatibleLocalData F ζ hζ)
    (x : rawB F ζ hζ P) (v : KPHilbert.Place F) :
    (rawCoordinate F ζ hζ P x v).val.val =
      KPPGLLocalCover.coverQuotient F ζ hζ v (x.val v) :=
  Classical.choose_spec (raw_coordinate_mem F ζ hζ P x v)

private theorem rawCoordinate_one (P : CompatibleLocalData F ζ hζ)
    (v : KPHilbert.Place F) : rawCoordinate F ζ hζ P 1 v = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  simpa using rawCoordinate_val F ζ hζ P 1 v

private theorem rawCoordinate_mul (P : CompatibleLocalData F ζ hζ)
    (x y : rawB F ζ hζ P) (v : KPHilbert.Place F) :
    rawCoordinate F ζ hζ P (x * y) v =
      rawCoordinate F ζ hζ P x v * rawCoordinate F ζ hζ P y v := by
  apply Subtype.ext
  apply Subtype.ext
  change (rawCoordinate F ζ hζ P (x * y) v).val.val =
    (rawCoordinate F ζ hζ P x v).val.val * (rawCoordinate F ζ hζ P y v).val.val
  rw [rawCoordinate_val, rawCoordinate_val, rawCoordinate_val]
  exact map_mul _ _ _

private theorem adjustedLocalValue_one (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (v : KPHilbert.Place F) :
    adjustedLocalValue F ζ hζ P T v 1 = 1 := by
  have h : (⟨localProjection F ζ hζ v (1 : localPreimage F ζ hζ v (P.localData v).L).val,
      (1 : localPreimage F ζ hζ v (P.localData v).L).property⟩ : (P.localData v).L) = 1 := by
    apply Subtype.ext
    exact map_one _
  simp only [adjustedLocalValue, map_one, one_mul, h]

private theorem adjustedLocalValue_mul (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (v : KPHilbert.Place F)
    (b c : localPreimage F ζ hζ v (P.localData v).L) :
    adjustedLocalValue F ζ hζ P T v (b * c) =
      adjustedLocalValue F ζ hζ P T v b * adjustedLocalValue F ζ hζ P T v c := by
  unfold adjustedLocalValue
  rw [map_mul]
  have h : (⟨localProjection F ζ hζ v (b * c).val, (b * c).property⟩ :
      (P.localData v).L) =
      ⟨localProjection F ζ hζ v b.val, b.property⟩ *
        ⟨localProjection F ζ hζ v c.val, c.property⟩ := by
    apply Subtype.ext
    exact map_mul _ _ _
  rw [h, map_mul]
  ac_rfl

theorem rawProduct_finiteSupport (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (x : rawB F ζ hζ P) :
    Function.HasFiniteMulSupport
      (fun v => adjustedLocalValue F ζ hζ P T v (rawCoordinate F ζ hζ P x v)) := by
  have hx : ∀ᶠ q in Filter.cofinite,
      x.val (Sum.inr q) ∈ KPAdelicCoverRestrictedProduct.compact F ζ hζ (Sum.inr q) :=
    Filter.eventually_cofinite.mpr
      ((Filter.eventually_cofinite.mp x.val.property).preimage Sum.inr_injective.injOn)
  have hS : ∀ᶠ q in Filter.cofinite, q ∉ T.S := by
    apply Filter.eventually_cofinite.mpr
    simpa using T.S.finite_toSet
  have hg : ∀ᶠ q in Filter.cofinite,
      adjustedLocalValue F ζ hζ P T (Sum.inr q) (rawCoordinate F ζ hζ P x (Sum.inr q)) = 1 := by
    filter_upwards [hx, P.unramified_almost_everywhere, hS] with q hq hu hS
    rw [adjustedLocalValue_outside F ζ hζ P T q hS]
    apply hu.2.2
    rw [rawCoordinate_val]
    exact Subgroup.mem_map.mpr ⟨x.val (Sum.inr q), hq, rfl⟩
  have hf := Filter.eventually_cofinite.mp hg
  apply Set.Finite.subset ((Set.finite_range (Sum.inl : InfinitePlace F → KPHilbert.Place F)).union
    (hf.image (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F)))
  intro v hv
  cases v with
  | inl w => exact Or.inl ⟨w, rfl⟩
  | inr q => exact Or.inr ⟨q, hv, rfl⟩

 theorem rawProduct_one (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) : rawProduct F ζ hζ P T 1 = 1 := by
  simp only [rawProduct, rawCoordinate_one, adjustedLocalValue_one, finprod_one]

 theorem rawProduct_mul (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (x y : rawB F ζ hζ P) :
    rawProduct F ζ hζ P T (x * y) =
      rawProduct F ζ hζ P T x * rawProduct F ζ hζ P T y := by
  unfold rawProduct
  simp only [rawCoordinate_mul, adjustedLocalValue_mul]
  exact finprod_mul_distrib (rawProduct_finiteSupport F ζ hζ P T x)
    (rawProduct_finiteSupport F ζ hζ P T y)

 def rawProductHom (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) : rawB F ζ hζ P →* ℂˣ where
  toFun := rawProduct F ζ hζ P T
  map_one' := rawProduct_one F ζ hζ P T
  map_mul' := rawProduct_mul F ζ hζ P T

theorem rawProduct_continuous (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) : Continuous (rawProduct F ζ hζ P T) := by
  exact (product_topology F ζ hζ P T).1

private theorem localValue_central (v : KPHilbert.Place F) (e : rootsOfUnity 3 F) :
    KPGlobalCenterRationalCharacter.localValue F ζ hζ v
      (KPLocalCover.centralInjection F ζ hζ v e) =
        KPGlobalTorusFunctionData.iota F ζ hζ e := by
  have hu : IsUnit ((KPLocalCover.centralInjection F ζ hζ v e).g 0 0) ∧
      IsUnit ((KPLocalCover.centralInjection F ζ hζ v e).g 1 1) := by
    constructor <;> exact isUnit_one
  rw [KPGlobalCenterRationalCharacter.localValue, dif_pos hu]
  have h1 : hu.1.unit = 1 := Units.ext hu.1.unit_spec
  have h2 : hu.2.unit = 1 := Units.ext hu.2.unit_spec
  simp only [h1, h2, inv_one, mul_one]
  have ha : KPGlobalCenterRationalCharacter.localAbs F v 1 = 1 := by
    cases v <;> simp [KPGlobalCenterRationalCharacter.localAbs]
  have hm : Units.mk0 (KPGlobalCenterRationalCharacter.localAbs F v 1)
    (ne_of_gt (KPGlobalCenterRationalCharacter.localAbs_pos F v 1)) = 1 := Units.ext ha
  simp only [hm, map_one, mul_one]
  rfl

private theorem rawCoordinate_central_projection (P : CompatibleLocalData F ζ hζ)
    (x : rawB F ζ hζ P) (v : KPHilbert.Place F) (e : rootsOfUnity 3 F)
    (hx : x.val v = KPLocalCover.centralInjection F ζ hζ v e) :
    localProjection F ζ hζ v (rawCoordinate F ζ hζ P x v).val = 1 := by
  have hq : KPPGLLocalCover.projection F ζ hζ v
      (rawCoordinate F ζ hζ P x v).val.val = 1 := by
    rw [rawCoordinate_val, hx, KPPGLLocalCover.projection_coverQuotient]
    simp
  have hr : localRatioValue F ζ hζ v (rawCoordinate F ζ hζ P x v).val = 1 := by
    symm
    apply localRatioValue_eq F ζ hζ v
    simpa using hq.symm
  change KPGlobalCubicIdelePairing.localClass F v
    (localRatioValue F ζ hζ v (rawCoordinate F ζ hζ P x v).val) = 1
  rw [hr, map_one]

theorem rawProduct_productOne (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (x : rawB F ζ hζ P)
    (hx : x.val ∈ KPAdelicCoverRestrictedProduct.M F ζ hζ) :
    rawProduct F ζ hζ P T x = 1 := by
  obtain ⟨e, he, hex⟩ := Subgroup.mem_map.mp hx
  have he1 : KPAdelicCoverRestrictedProduct.centralProduct F e = 1 := he
  have hval : ∀ v, adjustedLocalValue F ζ hζ P T v (rawCoordinate F ζ hζ P x v) =
      KPGlobalTorusFunctionData.iota F ζ hζ (e v) := by
    intro v
    have hxv : x.val v = KPLocalCover.centralInjection F ζ hζ v (e v) :=
      congrArg (fun a : KPGlobalCenterRationalCharacter.Raw F ζ hζ => a v) hex.symm
    have hp := rawCoordinate_central_projection F ζ hζ P x v (e v) hxv
    let z : localCenter F ζ hζ v := ⟨(rawCoordinate F ζ hζ P x v).val, hp⟩
    have hz : (rawCoordinate F ζ hζ P x v).val = z.val := rfl
    have hchi : (⟨localProjection F ζ hζ v (rawCoordinate F ζ hζ P x v).val,
        (rawCoordinate F ζ hζ P x v).property⟩ : (P.localData v).L) = 1 :=
      Subtype.ext hp
    unfold adjustedLocalValue
    rw [hchi, map_one, mul_one, (P.localData v).extends_center _ z hz]
    rw [localOmega_raw_formula F ζ hζ v z
      (KPLocalCover.centralInjection F ζ hζ v (e v))
      (by exact hxv ▸ (rawCoordinate_val F ζ hζ P x v).symm)]
    exact localValue_central F ζ hζ v (e v)
  unfold rawProduct
  simp only [hval]
  rw [← (KPGlobalTorusFunctionData.iota F ζ hζ).map_finprod
    (KPAdelicCoverRestrictedProduct.centralTuples_finiteSupport F e)]
  change KPGlobalTorusFunctionData.iota F ζ hζ
    (KPAdelicCoverRestrictedProduct.centralProduct F e) = 1
  rw [he1, map_one]

theorem rawProduct_splitScalar (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (u : KPGlobalCenterRationalCharacter.Ideles F)
    (x : rawB F ζ hζ P) (hx : x.val = KPAdelicCoverRestrictedProduct.scalarTuple F ζ hζ u) :
    rawProduct F ζ hζ P T x = 1 := by
  unfold rawProduct
  have hval : ∀ v, adjustedLocalValue F ζ hζ P T v (rawCoordinate F ζ hζ P x v) = 1 := by
    intro v
    have hq : KPPGLLocalCover.coverQuotient F ζ hζ v (x.val v) = 1 := by
      rw [hx]
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨Units.map (KPAdelicCoverRestrictedProduct.adeleEval F v) u, rfl⟩
    have hc : rawCoordinate F ζ hζ P x v = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact (rawCoordinate_val F ζ hζ P x v).trans hq
    rw [hc]
    exact adjustedLocalValue_one F ζ hζ P T v
  simp only [hval, finprod_one]

private theorem scalarTuple_mem_rawB (P : CompatibleLocalData F ζ hζ)
    (u : KPGlobalCenterRationalCharacter.Ideles F) :
    KPAdelicCoverRestrictedProduct.scalarTuple F ζ hζ u ∈ rawB F ζ hζ P := by
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.scalarHom F ζ hζ u) ∈
      (B F ζ hζ P).map (E F ζ hζ).subtype
  have h : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.scalarHom F ζ hζ u) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨u, rfl⟩
  rw [h]
  exact Subgroup.one_mem _

private theorem rawProduct_kernel (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (x : rawB F ζ hζ P)
    (hx : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = 1) :
    rawProduct F ζ hζ P T x = 1 := by
  obtain ⟨u, hu⟩ := (QuotientGroup.eq_one_iff _).mp hx
  let s : rawB F ζ hζ P := ⟨KPAdelicCoverRestrictedProduct.scalarTuple F ζ hζ u,
    scalarTuple_mem_rawB F ζ hζ P u⟩
  have hs : rawProduct F ζ hζ P T s = 1 :=
    rawProduct_splitScalar F ζ hζ P T u s rfl
  have hm : (x * s⁻¹).val ∈ KPAdelicCoverRestrictedProduct.M F ζ hζ := by
    apply (QuotientGroup.eq_one_iff _).mp
    change KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (x.val * s.val⁻¹) = 1
    rw [map_mul, map_inv]
    change KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val *
      (KPAdelicCoverRestrictedProduct.scalarHom F ζ hζ u)⁻¹ = 1
    rw [hu, mul_inv_cancel]
  have hprod := rawProduct_productOne F ζ hζ P T (x * s⁻¹) hm
  change rawProductHom F ζ hζ P T (x * s⁻¹) = 1 at hprod
  rw [map_mul, map_inv] at hprod
  change rawProductHom F ζ hζ P T s = 1 at hs
  change rawProductHom F ζ hζ P T x = 1
  simpa only [hs, inv_one, mul_one] using hprod

private theorem rawProduct_independent (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (x y : rawB F ζ hζ P)
    (hxy : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) =
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ y.val)) :
    rawProduct F ζ hζ P T x = rawProduct F ζ hζ P T y := by
  have hk : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (x * y⁻¹).val) = 1 := by
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (x.val * y.val⁻¹)) = 1
    rw [map_mul, map_inv, map_mul, map_inv, hxy, mul_inv_cancel]
  have h := rawProduct_kernel F ζ hζ P T (x * y⁻¹) hk
  change rawProductHom F ζ hζ P T (x * y⁻¹) = 1 at h
  rw [map_mul, map_inv, mul_inv_eq_one] at h
  exact h

theorem B_has_raw_lift (P : CompatibleLocalData F ζ hζ) (b : B F ζ hζ P) :
    ∃ x : rawB F ζ hζ P,
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = b.val.val := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    (KPAdelicCoverRestrictedProduct.splitScalarSubgroup F ζ hζ) b.val.val
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (KPAdelicCoverRestrictedProduct.M F ζ hζ) y
  have h : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x) = b.val.val :=
    (congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ) hx).trans hy
  refine ⟨⟨x, ?_⟩, h⟩
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x) ∈
      (B F ζ hζ P).map (E F ζ hζ).subtype
  rw [h]
  exact Subgroup.mem_map.mpr ⟨b.val, b.property, rfl⟩

def lambdaValue (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (b : B F ζ hζ P) : ℂˣ :=
  rawProduct F ζ hζ P T (Classical.choose (B_has_raw_lift F ζ hζ P b))

theorem lambdaValue_raw_formula (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (b : B F ζ hζ P) (x : rawB F ζ hζ P)
    (hx : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = b.val.val) :
    lambdaValue F ζ hζ P T b = rawProduct F ζ hζ P T x := by
  apply rawProduct_independent F ζ hζ P T
  exact (Classical.choose_spec (B_has_raw_lift F ζ hζ P b)).trans hx.symm

theorem lambdaValue_one (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) : lambdaValue F ζ hζ P T 1 = 1 := by
  rw [lambdaValue_raw_formula F ζ hζ P T 1 1 (by simp)]
  exact rawProduct_one F ζ hζ P T

theorem lambdaValue_mul (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (b c : B F ζ hζ P) :
    lambdaValue F ζ hζ P T (b * c) =
      lambdaValue F ζ hζ P T b * lambdaValue F ζ hζ P T c := by
  obtain ⟨x, hx⟩ := B_has_raw_lift F ζ hζ P b
  obtain ⟨y, hy⟩ := B_has_raw_lift F ζ hζ P c
  have hxy : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (x * y).val) = (b * c).val.val := by
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (x.val * y.val)) = b.val.val * c.val.val
    rw [map_mul, map_mul, hx, hy]
  rw [lambdaValue_raw_formula F ζ hζ P T (b * c) (x * y) hxy,
    lambdaValue_raw_formula F ζ hζ P T b x hx,
    lambdaValue_raw_formula F ζ hζ P T c y hy]
  exact rawProduct_mul F ζ hζ P T x y

theorem lambdaValue_continuous (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) : Continuous (lambdaValue F ζ hζ P T) := by
  have hq := (product_topology F ζ hζ P T).2
  apply hq.continuous_iff.mpr
  have heq : (lambdaValue F ζ hζ P T) ∘ rawProjection F ζ hζ P =
      rawProduct F ζ hζ P T := by
    funext x
    exact lambdaValue_raw_formula F ζ hζ P T _ x rfl
  exact heq.symm ▸ rawProduct_continuous F ζ hζ P T

def lambdaB (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) : B F ζ hζ P →ₜ* ℂˣ where
  toFun := lambdaValue F ζ hζ P T
  map_one' := lambdaValue_one F ζ hζ P T
  map_mul' := lambdaValue_mul F ζ hζ P T
  continuous_toFun := lambdaValue_continuous F ζ hζ P T

end FiniteAdjustmentSupport

namespace FiniteAdjustmentSupport

theorem diagonal_formula (t : KPGlobalTorusFunctionData.ordinaryTorus F) :
    KPGlobalCubicIdelePairing.diagonalPGL F (KPGlobalTorusFunctionData.torusRatio F t) = t.val := by
  let A := Classical.choose t.property
  have hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A = t.val ∧
      A 1 0 = 0 ∧ A 0 1 = 0 := Classical.choose_spec t.property
  let u := (KPGlobalTorusFunctionData.diagonal_entries_units F A hA.2.1 hA.2.2).1.unit
  let w := (KPGlobalTorusFunctionData.diagonal_entries_units F A hA.2.1 hA.2.2).2.unit
  have hu : (u : KPAdelicCoverRestrictedProduct.Adeles F) = A 0 0 := IsUnit.unit_spec _
  have hw : (w : KPAdelicCoverRestrictedProduct.Adeles F) = A 1 1 := IsUnit.unit_spec _
  have heq : A = KPGlobalCubicIdelePairing.diagonalHom F (u * w⁻¹) *
      Matrix.GeneralLinearGroup.scalar (Fin 2) w := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix,
        Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar, hu, hA.2.1, hA.2.2]
    exact hw.symm
  change QuotientGroup.mk' _ (KPGlobalCubicIdelePairing.diagonalHom F (u * w⁻¹)) = t.val
  rw [← hA.1, heq]
  have hs : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) w) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨w, rfl⟩
  rw [(QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).map_mul, hs, mul_one]
 def torusPullbackBridge : E F ζ hζ →* KPGlobalCubicIdelePairing.E F ζ hζ where
  toFun e := ⟨(e.val, KPGlobalTorusFunctionData.p F ζ hζ e),
    (diagonal_formula F ⟨_, e.property⟩).symm⟩
  map_one' := by apply Subtype.ext; exact Prod.ext rfl (map_one _)
  map_mul' x y := by apply Subtype.ext; exact Prod.ext rfl (map_mul _ _ _)

private theorem torusPullbackBridge_injective :
    Function.Injective (torusPullbackBridge F ζ hζ) := by
  intro x y h
  exact Subtype.ext (congrArg (fun t : KPGlobalCubicIdelePairing.E F ζ hζ => t.val.1) h)

private theorem commute_iff_beta (x y : E F ζ hζ) :
    Commute x y ↔ KPGlobalCubicIdelePairing.beta3 F ζ hζ
      (pD F ζ hζ x) (pD F ζ hζ y) = 1 := by
  have h := KPGlobalCubicIdelePairing.commutator_annihilators F ζ hζ
    (torusPullbackBridge F ζ hζ x) (torusPullbackBridge F ζ hζ y)
  constructor
  · intro hc
    exact h.mp (hc.map (torusPullbackBridge F ζ hζ))
  · intro hb
    apply torusPullbackBridge_injective F ζ hζ
    simpa only [map_mul] using (h.mpr hb).eq

def baseEval (v : KPHilbert.Place F) :
    KPAdelicCoverRestrictedProduct.AdelicPGL2 F →* KPPGLLocalCover.LocalPGL2 F v :=
  QuotientGroup.lift _ ((KPPGLLocalCover.baseQuotient F v).comp
    (KPAdelicCoverRestrictedProduct.matrixEval F v)) (by
      rintro a ⟨w, rfl⟩
      change KPPGLLocalCover.baseQuotient F v
        (KPAdelicCoverRestrictedProduct.matrixEval F v (Matrix.GeneralLinearGroup.scalar (Fin 2) w)) = 1
      apply (QuotientGroup.eq_one_iff _).mpr
      refine ⟨KPGlobalCubicIdelePairing.ideleEval F v w, ?_⟩
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [KPScalarSplitCentral.scalarMatrix, KPAdelicCoverRestrictedProduct.matrixEval,
          Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, KPGlobalCubicIdelePairing.ideleEval])
theorem eval_diagonal (v : KPHilbert.Place F) (y : KPGlobalCubicIdelePairing.Ideles F) :
    baseEval F v (KPGlobalCubicIdelePairing.diagonalPGL F y) =
      KPPGLLocalCover.baseQuotient F v (diagonalHom F v (KPGlobalCubicIdelePairing.ideleEval F v y)) := by
  change KPPGLLocalCover.baseQuotient F v
    (KPAdelicCoverRestrictedProduct.matrixEval F v (KPGlobalCubicIdelePairing.diagonalHom F y)) = _
  apply congrArg (KPPGLLocalCover.baseQuotient F v)
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [KPAdelicCoverRestrictedProduct.matrixEval, KPGlobalCubicIdelePairing.diagonalHom,
      KPGlobalCubicIdelePairing.diagonalMatrix, diagonalHom, KubotaRankTwo.coe_d,
      KPGlobalCubicIdelePairing.ideleEval]

def trivialAdjustment (P : CompatibleLocalData F ζ hζ) :
    FiniteAdjustment F ζ hζ P where
  S := ∅
  chi := fun _ => 1
  unitary := by intros; simp
  complex_unchanged := by intros; rfl
  outside_unchanged := by intros; rfl

theorem rawProjection_coord (P : CompatibleLocalData F ζ hζ)
    (x : rawB F ζ hζ P) (v : KPHilbert.Place F) :
    localProjection F ζ hζ v (rawCoordinate F ζ hζ P x v).val =
      KPGlobalCubicIdelePairing.classComparison F
        (pD F ζ hζ (rawProjection F ζ hζ P x).val) v := by
  let e : E F ζ hζ := (rawProjection F ζ hζ P x).val
  have hproj : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ e.val =
      KPGlobalCubicIdelePairing.diagonalPGL F (KPGlobalTorusFunctionData.p F ζ hζ e) :=
    (diagonal_formula F ⟨_, e.property⟩).symm
  have hlocal : KPPGLLocalCover.projection F ζ hζ v
      (rawCoordinate F ζ hζ P x v).val.val =
      KPPGLLocalCover.baseQuotient F v (diagonalHom F v
        (KPGlobalCubicIdelePairing.ideleEval F v (KPGlobalTorusFunctionData.p F ζ hζ e))) := by
    have h := congrArg (baseEval F v) hproj
    rw [eval_diagonal] at h
    change KPPGLLocalCover.baseQuotient F v
      (KPAdelicCoverRestrictedProduct.matrixEval F v
        (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ x.val)) = _ at h
    rw [KPAdelicCoverRestrictedProduct.restrictedProjection_eval] at h
    rw [rawCoordinate_val]
    exact h
  have hr := (localRatioValue_eq F ζ hζ v hlocal.symm).symm
  change KPGlobalCubicIdelePairing.localClass F v
    (localRatioValue F ζ hζ v (rawCoordinate F ζ hζ P x v).val) = _
  rw [hr]
  rfl

theorem pD_one_center (e : E F ζ hζ) (he : pD F ζ hζ e = 1) :
    e ∈ KPGlobalCenterRationalCharacter.Z F ζ hζ := by
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply (commute_iff_beta F ζ hζ y e).mpr
  rw [he]
  have h := (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).2.1 (pD F ζ hζ y) 1 1
  simpa only [one_mul, mul_eq_left] using h.symm

private theorem adjustment_product (P : CompatibleLocalData F ζ hζ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ψ : ((q : S) → (P.localData (Sum.inr q.val)).L) →* ℂˣ) :
    ∃ T : FiniteAdjustment F ζ hζ P,
      ∀ x : rawB F ζ hζ P,
        rawProduct F ζ hζ P T x =
          rawProduct F ζ hζ P (trivialAdjustment F ζ hζ P) x *
            ψ (fun q => ⟨localProjection F ζ hζ (Sum.inr q.val)
              (rawCoordinate F ζ hζ P x (Sum.inr q.val)).val,
                (rawCoordinate F ζ hζ P x (Sum.inr q.val)).property⟩) := by
  classical
  let chi (v : KPHilbert.Place F) : (P.localData v).L →* ℂˣ :=
    match v with
    | Sum.inl _ => 1
    | Sum.inr q => if h : q ∈ S then
        ψ.comp (MonoidHom.mulSingle (fun q : S => (P.localData (Sum.inr q.val)).L) ⟨q, h⟩)
      else 1
  letI : ∀ v, DiscreteTopology (LocalD F v) := local_discrete F
  let T : FiniteAdjustment F ζ hζ P := {
    S := S
    chi := fun v => { toMonoidHom := chi v, continuous_toFun := continuous_of_discreteTopology }
    unitary := by
      intro v x
      letI : Finite (LocalD F v) := local_finite F v
      exact ((Units.coeHom ℂ).comp (chi v) |>.isOfFinOrder
        (isOfFinOrder_of_finite x)).norm_eq_one
    complex_unchanged := by intro w; rfl
    outside_unchanged := by intro q hq; ext x; change (chi (Sum.inr q) x : ℂ) = 1; simp [chi, hq] }
  refine ⟨T, ?_⟩
  intro x
  let c (v : KPHilbert.Place F) := T.chi v
    ⟨localProjection F ζ hζ v (rawCoordinate F ζ hζ P x v).val,
      (rawCoordinate F ζ hζ P x v).property⟩
  have hc : Function.mulSupport c ⊆ (S.image Sum.inr : Finset (KPHilbert.Place F)) := by
    intro v hv
    cases v with
    | inl w => exact (hv rfl).elim
    | inr q =>
      have hq : q ∈ S := by
        by_contra hq
        exact hv (by change chi (Sum.inr q) _ = 1; simp [chi, hq])
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hcf : Function.HasFiniteMulSupport c := (S.image Sum.inr).finite_toSet.subset hc
  have hprod : (∏ᶠ v, c v) = ψ (fun q =>
      ⟨localProjection F ζ hζ (Sum.inr q.val)
        (rawCoordinate F ζ hζ P x (Sum.inr q.val)).val,
          (rawCoordinate F ζ hζ P x (Sum.inr q.val)).property⟩) := by
    rw [finprod_eq_prod_of_mulSupport_subset c hc,
      Finset.prod_image (by intro a ha b hb h; exact Sum.inr_injective h)]
    rw [← Finset.prod_coe_sort]
    simp only [c, T, chi, dif_pos (Subtype.property _)]
    change (∏ q : S, ψ (Pi.mulSingle q
      (⟨localProjection F ζ hζ (Sum.inr q.val)
        (rawCoordinate F ζ hζ P x (Sum.inr q.val)).val,
          (rawCoordinate F ζ hζ P x (Sum.inr q.val)).property⟩ :
            (P.localData (Sum.inr q.val)).L))) = _
    rw [← map_prod, Finset.univ_prod_mulSingle]
  have hi := rawProduct_finiteSupport F ζ hζ P (trivialAdjustment F ζ hζ P) x
  change (∏ᶠ v, (P.localData v).lambda (rawCoordinate F ζ hζ P x v) * c v) = _
  have hi' : Function.HasFiniteMulSupport
      (fun v => (P.localData v).lambda (rawCoordinate F ζ hζ P x v)) := by
    simpa [adjustedLocalValue, trivialAdjustment] using hi
  rw [finprod_mul_distrib hi' hcf, hprod]
  congr 1
  simp [rawProduct, adjustedLocalValue, trivialAdjustment]

end FiniteAdjustmentSupport

theorem finite_intersection_adjustment (P : CompatibleLocalData F ζ hζ) :
    ∃ T : FiniteAdjustment F ζ hζ P,
      ∀ (x : rawB F ζ hζ P) (r : KPGlobalCenterRationalCharacter.R F ζ hζ),
        KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = r.val.val →
        rawProduct F ζ hζ P T x = KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r := by
  classical
  let T₀ := FiniteAdjustmentSupport.trivialAdjustment F ζ hζ P
  let H := KPGlobalCenterRationalCharacter.R F ζ hζ ⊓ B F ζ hζ P
  let b : H →* B F ζ hζ P := (Subgroup.inclusion inf_le_right)
  let r : H →* KPGlobalCenterRationalCharacter.R F ζ hζ := (Subgroup.inclusion inf_le_left)
  let δ : H →* ℂˣ :=
    (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ).toMonoidHom.comp r /
      (FiniteAdjustmentSupport.lambdaB F ζ hζ P T₀).toMonoidHom.comp b
  obtain ⟨S, hS⟩ := FiniteAdjustmentSupport.exists_finite_coordinate_injection F ζ hζ P
  let V := (q : S) → (P.localData (Sum.inr q.val)).L
  let f : H →* V := MonoidHom.pi (fun q =>
    { toFun := fun h => ⟨KPGlobalCubicIdelePairing.classComparison F
        (pD F ζ hζ h.val) (Sum.inr q.val), h.property.2 (Sum.inr q.val)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; simp })
  have hk : f.ker ≤ δ.ker := by
    intro h hh
    have hj : pD F ζ hζ h.val ∈ J F ζ hζ P := by
      refine ⟨?_, h.property.2⟩
      have hr := h.property.1
      rw [KPGlobalCenterRationalCharacter.R_eq_principal_preimage F ζ hζ] at hr
      exact hr
    have hd : pD F ζ hζ h.val = 1 := by
      have hj1 : (⟨_, hj⟩ : J F ζ hζ P) = 1 := hS (by
        funext q
        have hq := congrArg Subtype.val (congrFun (show f h = 1 from hh) q)
        change KPGlobalCubicIdelePairing.classComparison F (pD F ζ hζ h.val)
          (Sum.inr q.val) = 1 at hq
        simpa using hq)
      exact congrArg Subtype.val hj1
    have hz := FiniteAdjustmentSupport.pD_one_center F ζ hζ h.val hd
    let z : KPGlobalCenterRationalCharacter.Z F ζ hζ := ⟨h.val, hz⟩
    have hb : FiniteAdjustmentSupport.lambdaB F ζ hζ P T₀ (b h) =
        KPGlobalCenterRationalCharacter.omegaA F ζ hζ z := by
      apply (product_character_values F ζ hζ P T₀
        (FiniteAdjustmentSupport.lambdaValue F ζ hζ P T₀)
        (FiniteAdjustmentSupport.lambdaValue_raw_formula F ζ hζ P T₀)).1 (b h) z rfl
    have hr : KPGlobalCenterRationalCharacter.lambdaR F ζ hζ (r h) =
        KPGlobalCenterRationalCharacter.omegaA F ζ hζ z := by
      exact KPGlobalCenterRationalCharacter.lambdaR_formula F ζ hζ (r h) 1 z (by simp [z, r])
    change KPGlobalCenterRationalCharacter.lambdaR F ζ hζ (r h) /
      FiniteAdjustmentSupport.lambdaB F ζ hζ P T₀ (b h) = 1
    rw [hr, hb, div_self']
  let d : f.range →* ℂˣ := f.rangeRestrict.liftOfSurjective
    f.rangeRestrict_surjective ⟨δ, by simpa using hk⟩
  letI : ∀ v, Finite (LocalD F v) := FiniteAdjustmentSupport.local_finite F
  obtain ⟨ψ, hψ⟩ := MonoidHom.domRestrict_surjective ℂ f.range d
  have hψf (h : H) : ψ (f h) = δ h := by
    change ψ (f.rangeRestrict h).val = δ h
    have hh := DFunLike.congr_fun hψ (f.rangeRestrict h)
    change ψ (f.rangeRestrict h).val = d (f.rangeRestrict h) at hh
    rw [hh]
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  obtain ⟨T, hT⟩ := FiniteAdjustmentSupport.adjustment_product F ζ hζ P S ψ
  refine ⟨T, ?_⟩
  intro x rr hx
  let bb := rawProjection F ζ hζ P x
  have he : bb.val = rr.val := Subtype.ext hx
  let h : H := ⟨rr.val, rr.property, he ▸ bb.property⟩
  have hc : (fun q : S =>
      (⟨localProjection F ζ hζ (Sum.inr q.val)
        (rawCoordinate F ζ hζ P x (Sum.inr q.val)).val,
          (rawCoordinate F ζ hζ P x (Sum.inr q.val)).property⟩ :
            (P.localData (Sum.inr q.val)).L)) = f h := by
    funext q
    apply Subtype.ext
    change localProjection F ζ hζ (Sum.inr q.val)
      (rawCoordinate F ζ hζ P x (Sum.inr q.val)).val =
        KPGlobalCubicIdelePairing.classComparison F (pD F ζ hζ h.val) (Sum.inr q.val)
    rw [FiniteAdjustmentSupport.rawProjection_coord]
    change KPGlobalCubicIdelePairing.classComparison F (pD F ζ hζ bb.val) _ = _
    rw [he]
  rw [hT x, hc, hψf]
  have hi : rawProduct F ζ hζ P T₀ x =
      FiniteAdjustmentSupport.lambdaB F ζ hζ P T₀ (b h) := by
    symm
    apply FiniteAdjustmentSupport.lambdaValue_raw_formula
    exact hx
  change rawProduct F ζ hζ P T₀ x = _ at hi
  rw [hi]
  change FiniteAdjustmentSupport.lambdaB F ζ hζ P T₀ (b h) *
    (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ (r h) /
      FiniteAdjustmentSupport.lambdaB F ζ hζ P T₀ (b h)) = _
  rw [mul_comm, div_mul_cancel]
  rfl

end
end DedekindZetaZeroFree.ProductPolarization
