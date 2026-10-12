module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteIntersectionCharacterAdjustment

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalProductPolarizationCharacter
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev D := KPGlobalCubicIdelePairing.D F
abbrev E := KPGlobalCenterRationalCharacter.E F ζ hζ
abbrev LocalD := KPGlobalCubicIdelePairing.LocalD F

attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology

def localCoverTopology (v : KPHilbert.Place F) :
    TopologicalSpace (KPPGLLocalCover.CubicPGL2 F ζ hζ v) := inferInstance

attribute [local instance] localCoverTopology

def diagonalHom (v : KPHilbert.Place F) :
    (KPHilbert.Completion F v)ˣ →* KPLocalCover.LocalGL2 F v where
  toFun y := KubotaRankTwo.d (KPHilbert.Completion F v) y 1
  map_one' := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

def localOrdinaryTorus (v : KPHilbert.Place F) :
    Subgroup (KPPGLLocalCover.LocalPGL2 F v) :=
  ((KPPGLLocalCover.baseQuotient F v).comp (diagonalHom F v)).range

def localTorus (v : KPHilbert.Place F) :
    Subgroup (KPPGLLocalCover.CubicPGL2 F ζ hζ v) :=
  (localOrdinaryTorus F v).comap (KPPGLLocalCover.projection F ζ hζ v)

abbrev LocalE (v : KPHilbert.Place F) := localTorus F ζ hζ v

def localRatioValue (v : KPHilbert.Place F) (g : LocalE F ζ hζ v) :
    (KPHilbert.Completion F v)ˣ := Classical.choose g.property

private theorem baseQuotient_diagonalHom_injective (v : KPHilbert.Place F) :
    Function.Injective fun y : (KPHilbert.Completion F v)ˣ =>
      KPPGLLocalCover.baseQuotient F v (diagonalHom F v y) := by
  intro y y' h
  simp only [KPPGLLocalCover.baseQuotient] at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨z, hzN, hz⟩ := h
  obtain ⟨w, hw⟩ := hzN
  have key : diagonalHom F v y * KPScalarSplitCentral.scalarMatrix F v w = diagonalHom F v y' := by
    rw [hw]; exact hz
  have h11 := congrArg (fun g : KPLocalCover.LocalGL2 F v =>
    (g : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 1 1) key
  have h00 := congrArg (fun g : KPLocalCover.LocalGL2 F v =>
    (g : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 0 0) key
  rw [Matrix.GeneralLinearGroup.coe_mul,
      show diagonalHom F v y = KubotaRankTwo.d (KPHilbert.Completion F v) y 1 from rfl,
      show diagonalHom F v y' = KubotaRankTwo.d (KPHilbert.Completion F v) y' 1 from rfl,
      KubotaRankTwo.coe_d, Matrix.GeneralLinearGroup.coe_scalar] at h11 h00
  simp [Matrix.scalar, Matrix.mul_apply, Fin.sum_univ_two] at h11 h00
  have hw1 : w = 1 := by
    apply Units.ext
    simpa using h11
  subst hw1
  exact Units.ext (by simpa using h00)

private theorem localRatioValue_spec (v : KPHilbert.Place F) (g : LocalE F ζ hζ v) :
    KPPGLLocalCover.baseQuotient F v (diagonalHom F v (localRatioValue F ζ hζ v g)) =
      KPPGLLocalCover.projection F ζ hζ v g :=
  Classical.choose_spec g.property

theorem localRatioValue_eq (v : KPHilbert.Place F) {g : LocalE F ζ hζ v}
    {y : (KPHilbert.Completion F v)ˣ}
    (hy : KPPGLLocalCover.baseQuotient F v (diagonalHom F v y) =
      KPPGLLocalCover.projection F ζ hζ v g) :
    y = localRatioValue F ζ hζ v g :=
  (baseQuotient_diagonalHom_injective F v
    ((localRatioValue_spec F ζ hζ v g).trans hy.symm).symm)

theorem localRatioValue_one (v : KPHilbert.Place F) :
    localRatioValue F ζ hζ v 1 = 1 := by
  symm
  apply localRatioValue_eq F ζ hζ v
  simp

theorem localRatioValue_mul (v : KPHilbert.Place F) (g h : LocalE F ζ hζ v) :
    localRatioValue F ζ hζ v (g * h) =
      localRatioValue F ζ hζ v g * localRatioValue F ζ hζ v h := by
  symm
  apply localRatioValue_eq F ζ hζ v (g := g * h)
  have hgh : KPPGLLocalCover.projection F ζ hζ v (↑(g * h) : KPPGLLocalCover.CubicPGL2 F ζ hζ v) =
      KPPGLLocalCover.projection F ζ hζ v ↑g * KPPGLLocalCover.projection F ζ hζ v ↑h := by
    rw [show (↑(g * h) : KPPGLLocalCover.CubicPGL2 F ζ hζ v) = ↑g * ↑h from rfl, map_mul]
  rw [hgh, ← localRatioValue_spec F ζ hζ v g, ← localRatioValue_spec F ζ hζ v h]
  rw [map_mul, map_mul]

def localRatio (v : KPHilbert.Place F) :
    LocalE F ζ hζ v →* (KPHilbert.Completion F v)ˣ where
  toFun := localRatioValue F ζ hζ v
  map_one' := localRatioValue_one F ζ hζ v
  map_mul' := localRatioValue_mul F ζ hζ v

def localProjection (v : KPHilbert.Place F) : LocalE F ζ hζ v →* LocalD F v :=
  (KPGlobalCubicIdelePairing.localClass F v).comp (localRatio F ζ hζ v)

def localCenter (v : KPHilbert.Place F) : Subgroup (LocalE F ζ hζ v) :=
  (localProjection F ζ hζ v).ker

theorem exists_local_omega (v : KPHilbert.Place F) :
    ∃ ω : localCenter F ζ hζ v →ₜ* ℂˣ,
      ∀ (z : localCenter F ζ hζ v) (g : KPLocalCover.CubicGL2Raw F ζ hζ v),
        KPPGLLocalCover.coverQuotient F ζ hζ v g = z.val.val →
        ω z = KPGlobalCenterRationalCharacter.localValue F ζ hζ v g := by
  exact (ProductPolarization.local_center_character F ζ hζ v).2

def localOmega (v : KPHilbert.Place F) : localCenter F ζ hζ v →ₜ* ℂˣ :=
  Classical.choose (exists_local_omega F ζ hζ v)

theorem localOmega_raw_formula (v : KPHilbert.Place F)
    (z : localCenter F ζ hζ v) (g : KPLocalCover.CubicGL2Raw F ζ hζ v)
    (hg : KPPGLLocalCover.coverQuotient F ζ hζ v g = z.val.val) :
    localOmega F ζ hζ v z = KPGlobalCenterRationalCharacter.localValue F ζ hζ v g :=
  Classical.choose_spec (exists_local_omega F ζ hζ v) z g hg

def IsMaximalIsotropic {G : Type*} [CommGroup G]
    (b : G → G → rootsOfUnity 3 F) (L : Subgroup G) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, b x y = 1) ∧
    ∀ N : Subgroup G, L ≤ N → (∀ x ∈ N, ∀ y ∈ N, b x y = 1) → N = L

def localPreimage (v : KPHilbert.Place F) (L : Subgroup (LocalD F v)) :
    Subgroup (LocalE F ζ hζ v) := L.comap (localProjection F ζ hζ v)

structure LocalPolarization (v : KPHilbert.Place F) where
  L : Subgroup (LocalD F v)
  maximal : IsMaximalIsotropic F (KPGlobalCubicIdelePairing.localPairing F ζ hζ v) L
  lambda : localPreimage F ζ hζ v L →ₜ* ℂˣ
  extends_center : ∀ (b : localPreimage F ζ hζ v L) (z : localCenter F ζ hζ v),
    b.val = z.val → lambda b = localOmega F ζ hζ v z
  modulus : ∀ b : localPreimage F ζ hζ v L,
    ‖(lambda b : ℂ)‖ = Real.rpow
      (KPGlobalCenterRationalCharacter.localAbs F v (localRatio F ζ hζ v b.val)) (1 / 6 : ℝ)

def IsUnramified (q : HeightOneSpectrum (𝓞 F))
    (P : LocalPolarization F ζ hζ (Sum.inr q)) : Prop :=
  ¬ KPAdelicCoverRestrictedProduct.Bad F q ∧
  P.L = KPGlobalCubicIdelePairing.U F (Sum.inr q) ∧
  ∀ b : localPreimage F ζ hζ (Sum.inr q) P.L,
    b.val.val ∈ KPAdelicCoverRestrictedProduct.pglCompact F ζ hζ (Sum.inr q) →
    P.lambda b = 1

structure CompatibleLocalData where
  localData : ∀ v : KPHilbert.Place F, LocalPolarization F ζ hζ v
  complex_full : ∀ w : InfinitePlace F, (localData (Sum.inl w)).L = ⊤
  unramified_almost_everywhere : ∀ᶠ q in Filter.cofinite,
    IsUnramified F ζ hζ q (localData (Sum.inr q))

 def toRawLocal (v : KPHilbert.Place F) (P : LocalPolarization F ζ hζ v) :
    ProductPolarization.LocalPolarization F ζ hζ v where
  L := P.L
  maximal := P.maximal
  lambda := P.lambda
  extends_center := P.extends_center
  modulus := P.modulus

def fromRawLocal (v : KPHilbert.Place F)
    (P : ProductPolarization.LocalPolarization F ζ hζ v) :
    LocalPolarization F ζ hζ v where
  L := P.L
  maximal := P.maximal
  lambda := P.lambda
  extends_center := P.extends_center
  modulus := P.modulus

def toRawData (P : CompatibleLocalData F ζ hζ) :
    ProductPolarization.CompatibleLocalData F ζ hζ where
  localData v := toRawLocal F ζ hζ v (P.localData v)
  complex_full := P.complex_full
  unramified_almost_everywhere := P.unramified_almost_everywhere

def restrictedM (P : CompatibleLocalData F ζ hζ) :
    Subgroup (KPGlobalCubicIdelePairing.RestrictedClasses F) where
  carrier := {x | ∀ v, x v ∈ (P.localData v).L}
  one_mem' := by intro v; exact (P.localData v).L.one_mem
  mul_mem' := by intro x y hx hy v; exact (P.localData v).L.mul_mem (hx v) (hy v)
  inv_mem' := by intro x hx v; exact (P.localData v).L.inv_mem (hx v)

def M (P : CompatibleLocalData F ζ hζ) : Subgroup (D F) :=
  (restrictedM F ζ hζ P).comap (KPGlobalCubicIdelePairing.classComparison F)

def pD : E F ζ hζ →* D F :=
  (QuotientGroup.mk' (CubicCharacters.cubes (KPGlobalCenterRationalCharacter.Ideles F))).comp
    (KPGlobalTorusFunctionData.p F ζ hζ)

def B (P : CompatibleLocalData F ζ hζ) : Subgroup (E F ζ hζ) :=
  (M F ζ hζ P).comap (pD F ζ hζ)

def J (P : CompatibleLocalData F ζ hζ) : Subgroup (D F) :=
  KPGlobalPrincipalCubicLagrangian.A F ⊓ M F ζ hζ P

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
private theorem local_finite (v : KPHilbert.Place F) : Finite (LocalD F v) := by
  cases v with
  | inl w => letI := KPGlobalCubicIdelePairing.local_complex_trivial F w; infer_instance
  | inr q =>
    letI : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
    letI : IsNonarchimedeanLocalField (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
    exact ClassFieldTheory.powerClassGroup_finite _ 3 (by norm_num)
private theorem local_discrete (v : KPHilbert.Place F) : DiscreteTopology (LocalD F v) := by
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

 def localPairingHom (v : KPHilbert.Place F) :
    LocalD F v →* (LocalD F v →* rootsOfUnity 3 F) where
  toFun x :=
    { toFun := KPGlobalCubicIdelePairing.localPairing F ζ hζ v x
      map_one' := by
        induction x using QuotientGroup.induction_on with
        | H x =>
          change KPGlobalCubicIdelePairing.localPairing F ζ hζ v
            (KPGlobalCubicIdelePairing.localClass F v x) 1 = 1
          rw [← map_one (KPGlobalCubicIdelePairing.localClass F v),
            KPGlobalCubicIdelePairing.localPairing_representatives]
          simpa only [one_pow] using ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.1 x 1).2
      map_mul' y z := by
        induction x using QuotientGroup.induction_on with
        | H x =>
          induction y using QuotientGroup.induction_on with
          | H y =>
            induction z using QuotientGroup.induction_on with
            | H z => exact (KPHilbert.B3_laws F ζ hζ v).2.1 x y z }
  map_one' := by
    apply MonoidHom.ext
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      change KPGlobalCubicIdelePairing.localPairing F ζ hζ v 1
        (KPGlobalCubicIdelePairing.localClass F v y) = 1
      rw [← map_one (KPGlobalCubicIdelePairing.localClass F v),
        KPGlobalCubicIdelePairing.localPairing_representatives]
      simpa only [one_pow] using ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.1 1 y).1
  map_mul' x y := by
    apply MonoidHom.ext
    intro z
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        induction z using QuotientGroup.induction_on with
        | H z => exact (KPHilbert.B3_laws F ζ hζ v).1 x y z

private theorem maximal_mem_of_annihilates {G : Type*} [CommGroup G]
    (b : G →* (G →* rootsOfUnity 3 F)) (halt : ∀ x, b x x = 1)
    (L : Subgroup G) (hL : IsMaximalIsotropic F (fun x y => b x y) L)
    (x : G) (hx : ∀ l ∈ L, b x l = 1) : x ∈ L := by
  have hswap (u v : G) : b v u = (b u v)⁻¹ := by
    have h := halt (v * u)
    simp only [map_mul, MonoidHom.mul_apply, halt, one_mul, mul_one] at h
    exact eq_inv_of_mul_eq_one_right h
  have hxl (l : G) (hl : l ∈ L) (n : ℤ) : b (x ^ n) l = 1 := by
    simp only [map_zpow, MonoidHom.zpow_apply, hx l hl, one_zpow]
  have hlx (l : G) (hl : l ∈ L) (n : ℤ) : b l (x ^ n) = 1 := by
    rw [hswap, hxl l hl n, inv_one]
  have hxx (n p : ℤ) : b (x ^ n) (x ^ p) = 1 := by
    simp only [map_zpow, MonoidHom.zpow_apply, halt, one_zpow]
  have hiso : ∀ u ∈ L ⊔ Subgroup.zpowers x, ∀ v ∈ L ⊔ Subgroup.zpowers x,
      b u v = 1 := by
    intro u hu v hv
    obtain ⟨l, hl, u', hu', rfl⟩ := Subgroup.mem_sup.mp hu
    obtain ⟨m, hm, v', hv', rfl⟩ := Subgroup.mem_sup.mp hv
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu'
    obtain ⟨p, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv'
    simp only [map_mul, MonoidHom.mul_apply, hL.1 l hl m hm,
      hlx l hl p, hxl m hm n, hxx n p, mul_one, one_mul]
  have heq := hL.2 _ le_sup_left hiso
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem M_maximal_isotropic (P : CompatibleLocalData F ζ hζ) :
    IsMaximalIsotropic F (KPGlobalCubicIdelePairing.beta3 F ζ hζ) (M F ζ hζ P) := by
  obtain ⟨e, he⟩ := KPGlobalCubicIdelePairing.restricted_cube_quotient F
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    change (∏ᶠ v, KPGlobalCubicIdelePairing.localPairing F ζ hζ v
      (KPGlobalCubicIdelePairing.classComparison F x v)
      (KPGlobalCubicIdelePairing.classComparison F y v)) = 1
    have h : ∀ v, KPGlobalCubicIdelePairing.localPairing F ζ hζ v
        (KPGlobalCubicIdelePairing.classComparison F x v)
        (KPGlobalCubicIdelePairing.classComparison F y v) = 1 := by
      intro v
      exact (P.localData v).maximal.1 _ (hx v) _ (hy v)
    simp only [h, finprod_one]
  · intro N hMN hN
    apply le_antisymm _ hMN
    intro x hx
    change ∀ v, KPGlobalCubicIdelePairing.classComparison F x v ∈ (P.localData v).L
    intro v
    apply maximal_mem_of_annihilates F (localPairingHom F ζ hζ v) ?_
      (P.localData v).L (P.localData v).maximal
    · intro l hl
      let t : KPGlobalCubicIdelePairing.RestrictedClasses F :=
        RestrictedProduct.mulSingle (KPGlobalCubicIdelePairing.U F) v l
      obtain ⟨y, hy⟩ := e.surjective t
      have hy' : KPGlobalCubicIdelePairing.classComparison F y = t := (he y).symm.trans hy
      have hym : y ∈ M F ζ hζ P := by
        change ∀ w, KPGlobalCubicIdelePairing.classComparison F y w ∈ (P.localData w).L
        intro w
        rw [hy']
        by_cases hw : w = v
        · subst w
          simpa only [t, RestrictedProduct.mulSingle_eq_same] using hl
        · simpa only [t, RestrictedProduct.mulSingle_eq_of_ne _ _ hw] using (P.localData w).L.one_mem
      have hxy := hN x hx y (hMN hym)
      change (∏ᶠ w, KPGlobalCubicIdelePairing.localPairing F ζ hζ w
        (KPGlobalCubicIdelePairing.classComparison F x w)
        (KPGlobalCubicIdelePairing.classComparison F y w)) = 1 at hxy
      rw [hy', finprod_eq_single _ v] at hxy
      · change KPGlobalCubicIdelePairing.localPairing F ζ hζ v
          (KPGlobalCubicIdelePairing.classComparison F x v) l = 1
        simpa only [t, RestrictedProduct.mulSingle_eq_same] using hxy
      · intro w hw
        rw [show t w = 1 from RestrictedProduct.mulSingle_eq_of_ne _ _ hw]
        exact (localPairingHom F ζ hζ w _).map_one
    · intro z
      induction z using QuotientGroup.induction_on with
      | H z => exact ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2 z).1

theorem B_maximal_abelian (P : CompatibleLocalData F ζ hζ) :
    KPLocalPolarization.IsMaximalAbelian (B F ζ hζ P) := by
  exact (ProductPolarization.product_polarization F ζ hζ (toRawData F ζ hζ P)).1

theorem B_closed (P : CompatibleLocalData F ζ hζ) :
    IsClosed (B F ζ hζ P : Set (E F ζ hζ)) := by
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hB := B_maximal_abelian F ζ hζ P
  letI : CommGroup (B F ζ hζ P) :=
    { (inferInstance : Group (B F ζ hζ P)) with
      mul_comm := fun x y => Subtype.ext (hB.1 x x.property y y.property).eq }
  letI := (B F ζ hζ P).commGroupTopologicalClosure
    (fun x y => mul_comm x y)
  have hc : (B F ζ hζ P).topologicalClosure = B F ζ hζ P := by
    apply hB.2 _ (B F ζ hζ P).le_topologicalClosure
    intro x hx y hy
    exact show Commute x y from
      (congrArg Subtype.val (mul_comm
        (⟨x, hx⟩ : (B F ζ hζ P).topologicalClosure) ⟨y, hy⟩))
  rw [← hc]
  exact (B F ζ hζ P).isClosed_topologicalClosure

theorem center_le_B (P : CompatibleLocalData F ζ hζ) :
    KPGlobalCenterRationalCharacter.Z F ζ hζ ≤ B F ζ hζ P := by
  have hB := B_maximal_abelian F ζ hζ P
  let C := B F ζ hζ P ⊔ KPGlobalCenterRationalCharacter.Z F ζ hζ
  have hcomm : ∀ x ∈ C, ∀ y ∈ C, Commute x y := by
    intro x hx y hy
    obtain ⟨bx, hbx, zx, hzx, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨cy, hcy, zy, hzy, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    have h1 : Commute bx zy := Subgroup.mem_center_iff.mp hzy bx
    have h2 : Commute zx cy := (Subgroup.mem_center_iff.mp hzx cy).symm
    have h3 : Commute zx zy := Subgroup.mem_center_iff.mp hzy zx
    exact ((hB.1 bx hbx cy hcy).mul_right h1).mul_left (h2.mul_right h3)
  have hCB : C = B F ζ hζ P := hB.2 C le_sup_left hcomm
  rw [← hCB]
  exact le_sup_right

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

theorem rational_intersection_preimage (P : CompatibleLocalData F ζ hζ) :
    KPGlobalCenterRationalCharacter.R F ζ hζ ⊓ B F ζ hζ P =
      (J F ζ hζ P).comap (pD F ζ hζ) := by
  rw [KPGlobalCenterRationalCharacter.R_eq_principal_preimage]
  rfl

structure FiniteAdjustment (P : CompatibleLocalData F ζ hζ) where
  S : Finset (HeightOneSpectrum (𝓞 F))
  chi : ∀ v : KPHilbert.Place F, (P.localData v).L →ₜ* ℂˣ
  unitary : ∀ v (x : (P.localData v).L), ‖(chi v x : ℂ)‖ = 1
  complex_unchanged : ∀ w : InfinitePlace F, chi (Sum.inl w) = 1
  outside_unchanged : ∀ q, q ∉ S → chi (Sum.inr q) = 1

 def toRawAdjustment (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) :
    ProductPolarization.FiniteAdjustment F ζ hζ (toRawData F ζ hζ P) where
  S := T.S
  chi := T.chi
  unitary := T.unitary
  complex_unchanged := T.complex_unchanged
  outside_unchanged := T.outside_unchanged

def fromRawAdjustment (P : CompatibleLocalData F ζ hζ)
    (T : ProductPolarization.FiniteAdjustment F ζ hζ (toRawData F ζ hζ P)) :
    FiniteAdjustment F ζ hζ P where
  S := T.S
  chi := T.chi
  unitary := T.unitary
  complex_unchanged := T.complex_unchanged
  outside_unchanged := T.outside_unchanged

def adjustedLocalValue (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (v : KPHilbert.Place F)
    (b : localPreimage F ζ hζ v (P.localData v).L) : ℂˣ :=
  (P.localData v).lambda b * T.chi v ⟨localProjection F ζ hζ v b.val, b.property⟩

theorem adjustedLocalValue_outside (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ T.S)
    (b : localPreimage F ζ hζ (Sum.inr q) (P.localData (Sum.inr q)).L) :
    adjustedLocalValue F ζ hζ P T (Sum.inr q) b = (P.localData (Sum.inr q)).lambda b := by
  simp [adjustedLocalValue, T.outside_unchanged q hq]

def rawB (P : CompatibleLocalData F ζ hζ) :
    Subgroup (KPGlobalCenterRationalCharacter.Raw F ζ hζ) :=
  ((B F ζ hζ P).map (E F ζ hζ).subtype).comap
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))

theorem raw_coordinate_mem (P : CompatibleLocalData F ζ hζ)
    (x : rawB F ζ hζ P) (v : KPHilbert.Place F) :
    ∃ b : localPreimage F ζ hζ v (P.localData v).L,
      b.val.val = KPPGLLocalCover.coverQuotient F ζ hζ v (x.val v) := by
  exact (ProductPolarization.product_polarization F ζ hζ (toRawData F ζ hζ P)).2 x v

def rawCoordinate (P : CompatibleLocalData F ζ hζ)
    (x : rawB F ζ hζ P) (v : KPHilbert.Place F) :
    localPreimage F ζ hζ v (P.localData v).L :=
  Classical.choose (raw_coordinate_mem F ζ hζ P x v)

 theorem rawCoordinate_val (P : CompatibleLocalData F ζ hζ)
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

def rawProduct (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (x : rawB F ζ hζ P) : ℂˣ :=
  ∏ᶠ v, adjustedLocalValue F ζ hζ P T v (rawCoordinate F ζ hζ P x v)

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
  exact (ProductPolarization.product_topology F ζ hζ (toRawData F ζ hζ P)
    (toRawAdjustment F ζ hζ P T)).1

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
  have hq := (ProductPolarization.product_topology F ζ hζ (toRawData F ζ hζ P)
    (toRawAdjustment F ζ hζ P T)).2
  apply hq.continuous_iff.mpr
  have heq : (lambdaValue F ζ hζ P T) ∘
      ProductPolarization.rawProjection F ζ hζ (toRawData F ζ hζ P) =
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

theorem lambdaB_extends_center (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (b : B F ζ hζ P)
    (z : KPGlobalCenterRationalCharacter.Z F ζ hζ) (hz : b.val = z.val) :
    lambdaB F ζ hζ P T b = KPGlobalCenterRationalCharacter.omegaA F ζ hζ z := by
  exact (ProductPolarization.product_character_values F ζ hζ (toRawData F ζ hζ P)
    (toRawAdjustment F ζ hζ P T) (lambdaValue F ζ hζ P T)
    (lambdaValue_raw_formula F ζ hζ P T)).1 b z hz

theorem lambdaB_norm (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (b : B F ζ hζ P) :
    ‖(lambdaB F ζ hζ P T b : ℂ)‖ =
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ b.val : ℝ≥0) : ℝ) := by
  exact (ProductPolarization.product_character_values F ζ hζ (toRawData F ζ hζ P)
    (toRawAdjustment F ζ hζ P T) (lambdaValue F ζ hζ P T)
    (lambdaValue_raw_formula F ζ hζ P T)).2 b

theorem lambdaB_raw_formula (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (b : B F ζ hζ P) (x : rawB F ζ hζ P)
    (hx : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = b.val.val) :
    lambdaB F ζ hζ P T b =
      ∏ᶠ v, adjustedLocalValue F ζ hζ P T v (rawCoordinate F ζ hζ P x v) := by
  change lambdaValue F ζ hζ P T b = rawProduct F ζ hζ P T x
  exact lambdaValue_raw_formula F ζ hζ P T b x hx

theorem exists_finite_compatible_adjustment (P : CompatibleLocalData F ζ hζ) :
    ∃ T : FiniteAdjustment F ζ hζ P,
      ∀ (b : B F ζ hζ P) (r : KPGlobalCenterRationalCharacter.R F ζ hζ),
        b.val = r.val →
        lambdaB F ζ hζ P T b = KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r := by
  obtain ⟨T, hT⟩ := ProductPolarization.finite_intersection_adjustment F ζ hζ
    (toRawData F ζ hζ P)
  refine ⟨fromRawAdjustment F ζ hζ P T, ?_⟩
  intro b r hbr
  obtain ⟨x, hx⟩ := B_has_raw_lift F ζ hζ P b
  rw [lambdaB_raw_formula F ζ hζ P _ b x hx]
  exact hT x (r) (hx.trans (congrArg Subtype.val hbr))

end
end DedekindZetaZeroFree.KPGlobalProductPolarizationCharacter

section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalProductPolarizationCharacter
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology

attribute [local instance] localCoverTopology

theorem exists_compatible_local_data : Nonempty (CompatibleLocalData F ζ hζ) := by
  obtain ⟨P⟩ := ProductPolarization.compatible_local_choices F ζ hζ
  exact ⟨{ localData := fun v => fromRawLocal F ζ hζ v (P.localData v)
           complex_full := P.complex_full
           unramified_almost_everywhere := P.unramified_almost_everywhere }⟩

end
end DedekindZetaZeroFree.KPGlobalProductPolarizationCharacter

end
