module

public import DedekindZetaZeroFree.Metaplectic.Torus.RestrictedTensorIdentification
public import DedekindZetaZeroFree.Metaplectic.Torus.RationalCompactOpenAnnihilator

@[expose] public section

open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStages
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev D := KPGlobalCubicIdelePairing.D F
abbrev E := KPGlobalTorusFunctionData.E F ζ hζ
abbrev A := KPGlobalPrincipalCubicLagrangian.A F
abbrev R := KPGlobalCenterRationalCharacter.R F ζ hζ
abbrev M (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ) :=
  KPGlobalProductPolarizationCharacter.M F ζ hζ P
abbrev B (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ) :=
  KPGlobalProductPolarizationCharacter.B F ζ hζ P
abbrev pD := KPGlobalProductPolarizationCharacter.pD F ζ hζ
abbrev J (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ) :=
  KPGlobalProductPolarizationCharacter.J F ζ hζ P

def rationalUnitValue (r : R F ζ hζ) : ℂˣ :=
  KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r /
    KPGlobalCenterRationalCharacter.positiveComplex
      (KPGlobalCenterRationalCharacter.nu F ζ hζ r.val)

def productUnitValue (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)
    (b : B F ζ hζ P) : ℂˣ :=
  KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T b /
    KPGlobalCenterRationalCharacter.positiveComplex
      (KPGlobalCenterRationalCharacter.nu F ζ hζ b.val)

def rationalUnitCharacter : R F ζ hζ →ₜ* ℂˣ where
  toFun := rationalUnitValue F ζ hζ
  map_one' := by simp [rationalUnitValue]
  map_mul' := by intros; simp [rationalUnitValue, map_mul, mul_div_mul_comm]
  continuous_toFun := by
    apply (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ).continuous.mul
    apply Continuous.inv
    exact (Units.continuous_map (Complex.continuous_ofReal.comp NNReal.continuous_coe)).comp
      ((KPGlobalCenterRationalCharacter.nu_continuous F ζ hζ).comp continuous_subtype_val)

def productUnitCharacter (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P) :
    B F ζ hζ P →ₜ* ℂˣ where
  toFun := productUnitValue F ζ hζ P T
  map_one' := by simp [productUnitValue]
  map_mul' := by intros; simp [productUnitValue, map_mul, mul_div_mul_comm]
  continuous_toFun := by
    apply (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T).continuous.mul
    apply Continuous.inv
    exact (Units.continuous_map (Complex.continuous_ofReal.comp NNReal.continuous_coe)).comp
      ((KPGlobalCenterRationalCharacter.nu_continuous F ζ hζ).comp continuous_subtype_val)

def annihilator (H : Subgroup (D F)) : Subgroup (D F) where
  carrier := {x | ∀ y ∈ H, KPGlobalCubicIdelePairing.beta3 F ζ hζ x y = 1}
  one_mem' := by
    intro y hy
    have h := (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1 1 1 y
    simpa using (mul_left_cancel (show
      KPGlobalCubicIdelePairing.beta3 F ζ hζ 1 y * KPGlobalCubicIdelePairing.beta3 F ζ hζ 1 y =
      KPGlobalCubicIdelePairing.beta3 F ζ hζ 1 y * 1 by simpa using h.symm))
  mul_mem' := by
    intro x z hx hz y hy
    rw [(KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1, hx y hy, hz y hy, one_mul]
  inv_mem' := by
    intro x hx y hy
    have h := (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1 x x⁻¹ y
    have h1 := (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1 1 1 y
    have he : KPGlobalCubicIdelePairing.beta3 F ζ hζ 1 y = 1 := by
      exact mul_left_cancel (show KPGlobalCubicIdelePairing.beta3 F ζ hζ 1 y *
        KPGlobalCubicIdelePairing.beta3 F ζ hζ 1 y =
        KPGlobalCubicIdelePairing.beta3 F ζ hζ 1 y * 1 by simpa using h1.symm)
    simpa [hx y hy, he] using h.symm

structure Level (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ) where
  K : Subgroup (D F)
  inside : K ≤ M F ζ hζ P
  compact : IsCompact (K : Set (D F))
  open' : IsOpen (K : Set (D F))
  transverse : K ⊓ A F = ⊥

instance (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ) :
    LE (Level F ζ hζ P) := ⟨fun L L' => L'.K ≤ L.K⟩

 def pairingKernel (y : D F) : Subgroup (D F) where
  carrier := {x | KPGlobalCubicIdelePairing.beta3 F ζ hζ x y = 1}
  one_mem' := (annihilator F ζ hζ ⊤).one_mem y (by trivial)
  mul_mem' := by
    intro x z hx hz
    change KPGlobalCubicIdelePairing.beta3 F ζ hζ (x * z) y = 1
    change KPGlobalCubicIdelePairing.beta3 F ζ hζ x y = 1 at hx
    change KPGlobalCubicIdelePairing.beta3 F ζ hζ z y = 1 at hz
    rw [(KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1, hx, hz, one_mul]
  inv_mem' := by
    intro x hx
    change KPGlobalCubicIdelePairing.beta3 F ζ hζ x y = 1 at hx
    have h := (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1 x x⁻¹ y
    have h1 := (annihilator F ζ hζ ⊤).one_mem y (by trivial)
    simpa [hx, h1] using h.symm

private theorem pairingKernel_open (y : D F) :
    IsOpen (pairingKernel F ζ hζ y : Set (D F)) := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  exact (isOpen_discrete ({1} : Set (rootsOfUnity 3 F))).preimage
    ((KPGlobalCubicIdelePairing.beta3_continuous F ζ hζ).comp
      (continuous_id.prodMk continuous_const))

private theorem small_level_exists
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (U : Subgroup (D F)) (hU : U ≤ M F ζ hζ P)
    (hOpen : IsOpen (U : Set (D F))) :
    ∃ L : Level F ζ hζ P, L.K ≤ U := by
  letI : Finite (J F ζ hζ P) := KPGlobalProductPolarizationCharacter.J_finite F ζ hζ P
  have hsep : ∀ j : J F ζ hζ P, ∃ y : D F,
      j.val ≠ 1 → KPGlobalCubicIdelePairing.beta3 F ζ hζ j.val y ≠ 1 := by
    intro j
    by_cases hj : j.val = 1
    · exact ⟨1, fun h => (h hj).elim⟩
    · have hn : ¬ ∀ y : D F, KPGlobalCubicIdelePairing.beta3 F ζ hζ j.val y = 1 := by
        intro hh
        exact hj ((KPGlobalCubicIdelePairing.beta3_radical_zero F ζ hζ j.val).mp hh)
      obtain ⟨y, hy⟩ := not_forall.mp hn
      exact ⟨y, fun _ => hy⟩
  choose y hy using hsep
  let K : Subgroup (D F) := U ⊓ ⨅ j : J F ζ hζ P, pairingKernel F ζ hζ (y j)
  have hKO : IsOpen (K : Set (D F)) := by
    change IsOpen ((U : Set (D F)) ∩ ↑(⨅ j : J F ζ hζ P, pairingKernel F ζ hζ (y j)))
    rw [Subgroup.coe_iInf]
    exact hOpen.inter (isOpen_iInter_of_finite (fun j => pairingKernel_open F ζ hζ (y j)))
  have hKM : K ≤ M F ζ hζ P := inf_le_left.trans hU
  refine ⟨⟨K, hKM, ?_, hKO, ?_⟩, inf_le_left⟩
  · exact (KPGlobalProductPolarizationCharacter.M_compact_open F ζ hζ P).1.of_isClosed_subset
      (K.isClosed_of_isOpen hKO) hKM
  · apply le_antisymm _ bot_le
    intro x hx
    let j : J F ζ hζ P := ⟨x, hx.2, hKM hx.1⟩
    have he : KPGlobalCubicIdelePairing.beta3 F ζ hζ x (y j) = 1 :=
      (Subgroup.mem_iInf.mp hx.1.2) j
    exact by
      change x = 1
      by_contra hn
      exact hy j hn he

theorem levels_nonempty (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ) :
    Nonempty (Level F ζ hζ P) := by
  obtain ⟨L, _⟩ := small_level_exists F ζ hζ P (M F ζ hζ P) le_rfl
    (KPGlobalProductPolarizationCharacter.M_compact_open F ζ hζ P).2
  exact ⟨L⟩

theorem levels_directed (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L L' : Level F ζ hζ P) :
    ∃ L'' : Level F ζ hζ P, L ≤ L'' ∧ L' ≤ L'' := by
  refine ⟨⟨L.K ⊓ L'.K, inf_le_left.trans L.inside, ?_,
    L.open'.inter L'.open', ?_⟩, (show L.K ⊓ L'.K ≤ L.K from inf_le_left),
    (show L.K ⊓ L'.K ≤ L'.K from inf_le_right)⟩
  · exact L.compact.inter_right (L'.K.isClosed_of_isOpen L'.open')
  · exact le_antisymm ((inf_le_inf_right (A F) inf_le_left).trans L.transverse.le) bot_le

theorem level_isotropic (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) : L.K ≤ annihilator F ζ hζ L.K := by
  intro x hx y hy
  exact (KPGlobalProductPolarizationCharacter.M_maximal_isotropic F ζ hζ P).1
    x (L.inside hx) y (L.inside hy)

 def betaLeft (y : D F) : D F →* rootsOfUnity 3 F where
  toFun x := KPGlobalCubicIdelePairing.beta3 F ζ hζ x y
  map_one' := (annihilator F ζ hζ ⊤).one_mem y (by trivial)
  map_mul' x z := (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1 x z y

 theorem beta_symmetric_one (x y : D F)
    (h : KPGlobalCubicIdelePairing.beta3 F ζ hζ x y = 1) :
    KPGlobalCubicIdelePairing.beta3 F ζ hζ y x = 1 := by
  have hb := KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ
  have hh := hb.2.2 (x * y)
  rw [hb.1, hb.2.1, hb.2.1, hb.2.2, hb.2.2, h] at hh
  simpa using hh

private theorem product_orthogonal_iff
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ) (x : D F) :
    (∀ y ∈ M F ζ hζ P, KPGlobalCubicIdelePairing.beta3 F ζ hζ x y = 1) ↔ x ∈ M F ζ hζ P := by
  constructor
  · intro hx
    have hb := KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ
    have hm := KPGlobalProductPolarizationCharacter.M_maximal_isotropic F ζ hζ P
    have hi : ∀ a ∈ M F ζ hζ P ⊔ Subgroup.zpowers x,
        ∀ b ∈ M F ζ hζ P ⊔ Subgroup.zpowers x,
          KPGlobalCubicIdelePairing.beta3 F ζ hζ a b = 1 := by
      intro a ha b hb'
      obtain ⟨m, hm', z, hz, rfl⟩ := Subgroup.mem_sup.mp ha
      obtain ⟨n, hn, w, hw, rfl⟩ := Subgroup.mem_sup.mp hb'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hxn : KPGlobalCubicIdelePairing.beta3 F ζ hζ (x ^ i) n = 1 := by
        change betaLeft F ζ hζ n (x ^ i) = 1
        rw [map_zpow]
        change KPGlobalCubicIdelePairing.beta3 F ζ hζ x n ^ i = 1
        rw [hx n hn, one_zpow]
      have hxm : KPGlobalCubicIdelePairing.beta3 F ζ hζ m (x ^ j) = 1 := by
        apply beta_symmetric_one F ζ hζ
        change betaLeft F ζ hζ m (x ^ j) = 1
        rw [map_zpow]
        change KPGlobalCubicIdelePairing.beta3 F ζ hζ x m ^ j = 1
        rw [hx m hm', one_zpow]
      have hxx : KPGlobalCubicIdelePairing.beta3 F ζ hζ (x ^ i) (x ^ j) = 1 := by
        have hxxj : KPGlobalCubicIdelePairing.beta3 F ζ hζ x (x ^ j) = 1 := by
          apply beta_symmetric_one F ζ hζ
          change betaLeft F ζ hζ x (x ^ j) = 1
          rw [map_zpow]
          change KPGlobalCubicIdelePairing.beta3 F ζ hζ x x ^ j = 1
          rw [hb.2.2, one_zpow]
        change betaLeft F ζ hζ (x ^ j) (x ^ i) = 1
        rw [map_zpow]
        change KPGlobalCubicIdelePairing.beta3 F ζ hζ x (x ^ j) ^ i = 1
        rw [hxxj, one_zpow]
      rw [hb.1, hb.2.1, hb.2.1, hm.1 m hm' n hn, hxn, hxm, hxx]
      simp
    have he := hm.2 (M F ζ hζ P ⊔ Subgroup.zpowers x) le_sup_left hi
    change x ∈ KPGlobalProductPolarizationCharacter.M F ζ hζ P
    rw [← he]
    exact (show Subgroup.zpowers x ≤ M F ζ hζ P ⊔ Subgroup.zpowers x from le_sup_right)
      (Subgroup.mem_zpowers x)
  · intro hx y hy
    exact (KPGlobalProductPolarizationCharacter.M_maximal_isotropic F ζ hζ P).1 x hx y hy

 def betaRight (x : D F) : D F →* rootsOfUnity 3 F where
  toFun y := KPGlobalCubicIdelePairing.beta3 F ζ hζ x y
  map_one' := by
    have h := beta_symmetric_one F ζ hζ 1 x ((betaLeft F ζ hζ x).map_one)
    exact h
  map_mul' y z := (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).2.1 x y z

private theorem product_in_annihilator
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) : M F ζ hζ P ≤ annihilator F ζ hζ L.K := by
  intro x hx y hy
  exact (KPGlobalProductPolarizationCharacter.M_maximal_isotropic F ζ hζ P).1 x hx y (L.inside hy)

private theorem annihilator_quotient_product_finite
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) :
    Finite ((annihilator F ζ hζ L.K) ⧸ ((M F ζ hζ P).comap (annihilator F ζ hζ L.K).subtype)) := by
  let N := annihilator F ζ hζ L.K
  let H := (M F ζ hζ P).comap N.subtype
  let KM := L.K.comap (M F ζ hζ P).subtype
  letI : CompactSpace (M F ζ hζ P) := isCompact_iff_compactSpace.mp
    (KPGlobalProductPolarizationCharacter.M_compact_open F ζ hζ P).1
  letI : Finite ((M F ζ hζ P) ⧸ KM) :=
    Subgroup.quotient_finite_of_isOpen KM (L.open'.preimage continuous_subtype_val)
  let value : N → ((M F ζ hζ P) ⧸ KM) → rootsOfUnity 3 F := fun x =>
    QuotientGroup.lift KM ((betaRight F ζ hζ x.val).comp (M F ζ hζ P).subtype)
      (by intro k hk; exact x.property k.val hk)
  let φ : N →* (((M F ζ hζ P) ⧸ KM) → rootsOfUnity 3 F) :=
    { toFun := value
      map_one' := by
        funext z
        induction z using QuotientGroup.induction_on with
        | H m => exact (betaLeft F ζ hζ m.val).map_one
      map_mul' := by
        intro x y
        funext z
        induction z using QuotientGroup.induction_on with
        | H m => exact (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1 x.val y.val m.val }
  have hker : H ≤ φ.ker := by
    intro x hx
    funext z
    induction z using QuotientGroup.induction_on with
    | H m => exact (KPGlobalProductPolarizationCharacter.M_maximal_isotropic F ζ hζ P).1 x.val hx m.val m.property
  let ψ := QuotientGroup.lift H φ hker
  apply Finite.of_injective ψ
  apply (injective_iff_map_eq_one ψ).mpr
  intro z
  induction z using QuotientGroup.induction_on with
  | H x =>
    intro hx
    apply (QuotientGroup.eq_one_iff x).mpr
    apply (product_orthogonal_iff F ζ hζ P x.val).mp
    intro m hm
    exact congrFun hx (QuotientGroup.mk' KM ⟨m, hm⟩)

theorem annihilator_compact_open
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) :
    IsCompact (annihilator F ζ hζ L.K : Set (D F)) ∧
      IsOpen (annihilator F ζ hζ L.K : Set (D F)) := by
  have hMN := product_in_annihilator F ζ hζ P L
  have hOpen : IsOpen (annihilator F ζ hζ L.K : Set (D F)) :=
    Subgroup.isOpen_mono hMN (KPGlobalProductPolarizationCharacter.M_compact_open F ζ hζ P).2
  refine ⟨?_, hOpen⟩
  let N := annihilator F ζ hζ L.K
  let H := (M F ζ hζ P).comap N.subtype
  letI : Finite (N ⧸ H) := annihilator_quotient_product_finite F ζ hζ P L
  have hs : ∀ z : N ⧸ H, ∃ x : N, QuotientGroup.mk' H x = z := QuotientGroup.mk'_surjective H
  choose reps hreps using hs
  have he : (N : Set (D F)) = ⋃ z : N ⧸ H,
      (fun m : D F => (reps z).val * m) '' (M F ζ hζ P : Set (D F)) := by
    ext x
    constructor
    · intro hx
      let n : N := ⟨x, hx⟩
      let z := QuotientGroup.mk' H n
      have hh : QuotientGroup.mk' H (reps z) = QuotientGroup.mk' H n := hreps z
      have hm : (reps z).val⁻¹ * x ∈ M F ζ hζ P :=
        (QuotientGroup.eq (a := reps z) (b := n)).mp hh
      exact Set.mem_iUnion.mpr ⟨z, (reps z).val⁻¹ * x, hm, mul_inv_cancel_left _ _⟩
    · intro hx
      obtain ⟨z, m, hm, rfl⟩ := Set.mem_iUnion.mp hx
      exact N.mul_mem (reps z).property (hMN hm)
  rw [he]
  exact isCompact_iUnion (fun z => (KPGlobalProductPolarizationCharacter.M_compact_open F ζ hζ P).1.image
    (continuous_const.mul continuous_id))

abbrev symplecticQuotient (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) :=
  (annihilator F ζ hζ L.K) ⧸ (L.K.comap (annihilator F ζ hζ L.K).subtype)

def quotientClass (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) (x : annihilator F ζ hζ L.K) :
    symplecticQuotient F ζ hζ P L :=
  QuotientGroup.mk' _ x

theorem quotient_finite (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) : Finite (symplecticQuotient F ζ hζ P L) := by
  letI : CompactSpace (annihilator F ζ hζ L.K) :=
    isCompact_iff_compactSpace.mp (annihilator_compact_open F ζ hζ P L).1
  exact Subgroup.quotient_finite_of_isOpen _
    (L.open'.preimage continuous_subtype_val)

theorem product_inside_annihilator
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) : M F ζ hζ P ≤ annihilator F ζ hζ L.K := by
  intro x hx y hy
  exact (KPGlobalProductPolarizationCharacter.M_maximal_isotropic F ζ hζ P).1
    x hx y (L.inside hy)

structure CompatibleModelData where
  localData : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ
  adjustment : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ localData
  agrees : ∀ (b : B F ζ hζ localData) (r : R F ζ hζ), b.val = r.val →
    KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ localData adjustment b =
      KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r

instance : Coe (CompatibleModelData F ζ hζ)
    (KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ) := ⟨fun P => P.localData⟩

def compatibleAdjustment (P : CompatibleModelData F ζ hζ) := P.adjustment

def rationalModel : KPGlobalTorusFunctionData.Polarization F ζ hζ where
  H := R F ζ hζ
  closed := KPGlobalCenterRationalCharacter.R_closed F ζ hζ
  abelian := by
    intro h k
    apply Subtype.ext
    exact (KPGlobalCenterRationalCharacter.R_maximal_abelian F ζ hζ).1 h.val h.property k.val k.property
  contains_center := by
    exact le_sup_right
  character := rationalUnitCharacter F ζ hζ

def productModel
    (P : CompatibleModelData F ζ hζ) :
    KPGlobalTorusFunctionData.Polarization F ζ hζ where
  H := B F ζ hζ P
  closed := KPGlobalProductPolarizationCharacter.B_closed F ζ hζ P
  abelian := by
    intro h k
    apply Subtype.ext
    exact (KPGlobalProductPolarizationCharacter.B_maximal_abelian F ζ hζ P).1 h.val h.property k.val k.property
  contains_center := KPGlobalProductPolarizationCharacter.center_le_B F ζ hζ P
  character := productUnitCharacter F ζ hζ P (compatibleAdjustment F ζ hζ P)

def stageDomain
    (P : CompatibleModelData F ζ hζ)
    (L : Level F ζ hζ P) : Subgroup (E F ζ hζ) :=
  (annihilator F ζ hζ L.K).comap (pD F ζ hζ)

def phaseGroup
    (P : CompatibleModelData F ζ hζ)
    (L : Level F ζ hζ P) : Subgroup (E F ζ hζ) := L.K.comap (pD F ζ hζ)

theorem phase_inside_product
    (P : CompatibleModelData F ζ hζ)
    (L : Level F ζ hζ P) : phaseGroup F ζ hζ P L ≤ B F ζ hζ P := by
  intro g hg
  exact L.inside hg

theorem phase_inside_domain
    (P : CompatibleModelData F ζ hζ)
    (L : Level F ζ hζ P) : phaseGroup F ζ hζ P L ≤ stageDomain F ζ hζ P L := by
  intro g hg
  exact level_isotropic F ζ hζ P L hg

def phaseCharacter
    (P : CompatibleModelData F ζ hζ)
    (L : Level F ζ hζ P) : phaseGroup F ζ hζ P L →* ℂˣ :=
  (productUnitCharacter F ζ hζ P (compatibleAdjustment F ζ hζ P)).toMonoidHom.comp
    (Subgroup.inclusion (phase_inside_product F ζ hζ P L))

def phaseElement
    (P : CompatibleModelData F ζ hζ)
    (L : Level F ζ hζ P) (k : phaseGroup F ζ hζ P L) : stageDomain F ζ hζ P L :=
  ⟨k.val, phase_inside_domain F ζ hζ P L k.property⟩

def RestrictedSections
    (P : CompatibleModelData F ζ hζ)
    (L : Level F ζ hζ P) (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) :
    Submodule ℂ (stageDomain F ζ hζ P L → ℂ) where
  carrier := {f |
    (∀ (h : Q.H.comap (stageDomain F ζ hζ P L).subtype)
        (x : stageDomain F ζ hζ P L),
      f (h.val * x) = (Q.character ⟨h.val.val, h.property⟩ : ℂ) * f x) ∧
    (∀ (k : phaseGroup F ζ hζ P L) (x : stageDomain F ζ hζ P L),
      f (x * phaseElement F ζ hζ P L k) =
        (phaseCharacter F ζ hζ P L k : ℂ) * f x)}
  zero_mem' := by constructor <;> intros <;> simp
  add_mem' := by
    intro f g hf hg
    constructor
    · intro h x; simp [hf.1 h x, hg.1 h x, mul_add]
    · intro k x; simp [hf.2 k x, hg.2 k x, mul_add]
  smul_mem' := by
    intro c f hf
    constructor
    · intro h x; simp only [Pi.smul_apply, smul_eq_mul, hf.1 h x]; ring
    · intro k x; simp only [Pi.smul_apply, smul_eq_mul, hf.2 k x]; ring

def saturatedDomain
    (P : CompatibleModelData F ζ hζ)
    (L : Level F ζ hζ P) (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) :
    Set (E F ζ hζ) :=
  {g | ∃ (h : Q.H) (x : stageDomain F ζ hζ P L), g = h.val * x.val}

def Stage
    (P : CompatibleModelData F ζ hζ)
    (L : Level F ζ hζ P) (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) :
    Submodule ℂ (KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q) where
  carrier := {f |
    (∀ g, g ∉ saturatedDomain F ζ hζ P L Q → f.val g = 0) ∧
    (∀ (k : phaseGroup F ζ hζ P L) (x : stageDomain F ζ hζ P L),
      f.val (x.val * k.val) = (phaseCharacter F ζ hζ P L k : ℂ) * f.val x.val)}
  zero_mem' := by constructor <;> intros <;> simp
  add_mem' := by
    intro f g hf hg
    constructor
    · intro x hx; simp [hf.1 x hx, hg.1 x hx]
    · intro k x; simp [hf.2 k x, hg.2 k x, mul_add]
  smul_mem' := by
    intro c f hf
    constructor
    · intro x hx; simp [hf.1 x hx]
    · intro k x; simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
        hf.2 k x]; ring

def restriction
    (P : CompatibleModelData F ζ hζ)
    (L : Level F ζ hζ P) (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) :
    Stage F ζ hζ P L Q →ₗ[ℂ] RestrictedSections F ζ hζ P L Q where
  toFun f := ⟨fun x => f.val.val x.val, by
    constructor
    · intro h x
      exact f.val.property ⟨h.val.val, h.property⟩ x.val
    · intro k x
      exact f.property.2 k x⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

 def covarianceExtension {G : Type*} [Group G] (H S : Subgroup G)
    (χ : H →* ℂˣ) (f : S → ℂ) (g : G) : ℂ :=
  if hg : ∃ (h : H) (x : S), g = h.val * x.val then
    (χ (Classical.choose hg) : ℂ) * f (Classical.choose (Classical.choose_spec hg))
  else 0

private theorem covarianceExtension_formula {G : Type*} [Group G] (H S : Subgroup G)
    (χ : H →* ℂˣ) (f : S → ℂ)
    (hf : ∀ (h : H.comap S.subtype) (x : S),
      f (h.val * x) = (χ ⟨h.val.val, h.property⟩ : ℂ) * f x)
    (h : H) (x : S) : covarianceExtension H S χ f (h.val * x.val) = (χ h : ℂ) * f x := by
  have hg : ∃ (a : H) (y : S), h.val * x.val = a.val * y.val := ⟨h, x, rfl⟩
  rw [covarianceExtension, dif_pos hg]
  let a := Classical.choose hg
  let y := Classical.choose (Classical.choose_spec hg)
  have he : h.val * x.val = a.val * y.val := Classical.choose_spec (Classical.choose_spec hg)
  have hk : a.val⁻¹ * h.val = y.val * x.val⁻¹ := by
    have hh := congrArg (fun g => a.val⁻¹ * g * x.val⁻¹) he
    simpa only [mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel_left] using hh
  let k : H.comap S.subtype := ⟨⟨a.val⁻¹ * h.val, hk ▸ S.mul_mem y.property (S.inv_mem x.property)⟩,
    H.mul_mem (H.inv_mem a.property) h.property⟩
  have hy : k.val * x = y := by
    apply Subtype.ext
    change (a.val⁻¹ * h.val) * x.val = y.val
    rw [hk, mul_assoc, inv_mul_cancel, mul_one]
  have hh : (⟨k.val.val, k.property⟩ : H) = a⁻¹ * h := rfl
  have hv := hf k x
  rw [hy, hh, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val] at hv
  change (χ a : ℂ) * f y = (χ h : ℂ) * f x
  rw [hv]
  have hne : (χ a : ℂ) ≠ 0 := Units.ne_zero (χ a)
  field_simp

private theorem covarianceExtension_covariance {G : Type*} [Group G] (H S : Subgroup G)
    (χ : H →* ℂˣ) (f : S → ℂ)
    (hf : ∀ (h : H.comap S.subtype) (x : S),
      f (h.val * x) = (χ ⟨h.val.val, h.property⟩ : ℂ) * f x)
    (h : H) (g : G) : covarianceExtension H S χ f (h.val * g) =
      (χ h : ℂ) * covarianceExtension H S χ f g := by
  by_cases hg : ∃ (a : H) (x : S), g = a.val * x.val
  · obtain ⟨a, x, rfl⟩ := hg
    rw [← mul_assoc]
    change covarianceExtension H S χ f ((h * a).val * x.val) = _
    rw [covarianceExtension_formula H S χ f hf,
      covarianceExtension_formula H S χ f hf, map_mul, Units.val_mul, mul_assoc]
  · have hh : ¬ ∃ (a : H) (x : S), h.val * g = a.val * x.val := by
      rintro ⟨a, x, he⟩
      apply hg
      refine ⟨h⁻¹ * a, x, ?_⟩
      have hh := congrArg (fun z => h.val⁻¹ * z) he
      simpa only [mul_assoc, inv_mul_cancel_left, Subgroup.coe_mul, Subgroup.coe_inv] using hh
    simp only [covarianceExtension, dif_neg hg, dif_neg hh, mul_zero]

theorem restriction_bijective
    (P : CompatibleModelData F ζ hζ)
    (L : Level F ζ hζ P) (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : Q = rationalModel F ζ hζ ∨ Q = productModel F ζ hζ P) :
    Function.Bijective (restriction F ζ hζ P L Q) := by
  constructor
  · intro f g he
    apply Subtype.ext
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ saturatedDomain F ζ hζ P L Q
    · obtain ⟨h, y, rfl⟩ := hx
      rw [f.val.property h y.val, g.val.property h y.val]
      exact congrArg (fun t : RestrictedSections F ζ hζ P L Q => (Q.character h : ℂ) * t.val y) he
    · rw [f.property.1 x hx, g.property.1 x hx]
  · intro f
    let v := covarianceExtension Q.H (stageDomain F ζ hζ P L) Q.character.toMonoidHom f.val
    have hv : ∀ (h : Q.H) (x : stageDomain F ζ hζ P L),
        v (h.val * x.val) = (Q.character h : ℂ) * f.val x :=
      covarianceExtension_formula _ _ _ _ f.property.1
    let t : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q :=
      ⟨v, covarianceExtension_covariance _ _ _ _ f.property.1⟩
    have ht : t ∈ Stage F ζ hζ P L Q := by
      constructor
      · intro g hg
        exact dif_neg hg
      · intro k x
        have hh := hv 1 (x * phaseElement F ζ hζ P L k)
        have hx := hv 1 x
        simp only [Subgroup.coe_one, one_mul, map_one, Units.val_one] at hh hx
        change v (x.val * k.val) = (phaseCharacter F ζ hζ P L k : ℂ) * v x.val
        change v (x.val * k.val) = f.val (x * phaseElement F ζ hζ P L k) at hh
        rw [hh, hx]
        exact f.property.2 k x
    refine ⟨⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    funext x
    change v x.val = f.val x
    have hx := hv 1 x
    simpa only [Subgroup.coe_one, one_mul, map_one, Units.val_one] using hx

set_option maxHeartbeats 1000000 in
theorem stage_module_finite
    (P : CompatibleModelData F ζ hζ)
    (L : Level F ζ hζ P) (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : Q = rationalModel F ζ hζ ∨ Q = productModel F ζ hζ P) :
    Module.Finite ℂ (Stage F ζ hζ P L Q) := by
  letI : Finite (symplecticQuotient F ζ hζ P L) := quotient_finite F ζ hζ P L
  let c : stageDomain F ζ hζ P L → symplecticQuotient F ζ hζ P L := fun x =>
    quotientClass F ζ hζ P L ⟨pD F ζ hζ x.val, x.property⟩
  have hex : ∀ z : symplecticQuotient F ζ hζ P L,
      ∃ x : stageDomain F ζ hζ P L, (∃ y, c y = z) → c x = z := by
    intro z
    by_cases hz : ∃ y, c y = z
    · obtain ⟨y, hy⟩ := hz
      exact ⟨y, fun _ => hy⟩
    · exact ⟨1, fun h => (hz h).elim⟩
  choose reps hreps using hex
  let ev : Stage F ζ hζ P L Q →ₗ[ℂ] (symplecticQuotient F ζ hζ P L → ℂ) :=
    { toFun := fun f z => f.val.val (reps z).val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply Module.Finite.of_injective ev
  intro f g he
  apply (restriction_bijective F ζ hζ P L Q hQ).1
  apply Subtype.ext
  funext x
  let r := reps (c x)
  have hr : c r = c x := hreps (c x) ⟨x, rfl⟩
  have hk : pD F ζ hζ (r.val⁻¹ * x.val) ∈ L.K := by
    have hh := (QuotientGroup.eq
      (a := (⟨pD F ζ hζ r.val, r.property⟩ : annihilator F ζ hζ L.K))
      (b := (⟨pD F ζ hζ x.val, x.property⟩ : annihilator F ζ hζ L.K))).mp hr
    rw [map_mul, map_inv]
    exact hh
  let k : phaseGroup F ζ hζ P L := ⟨r.val⁻¹ * x.val, hk⟩
  have hx : r.val * k.val = x.val := mul_inv_cancel_left r.val x.val
  change f.val.val x.val = g.val.val x.val
  rw [← hx, f.property.2 k r, g.property.2 k r]
  exact congrArg (fun t : symplecticQuotient F ζ hζ P L → ℂ =>
    (phaseCharacter F ζ hζ P L k : ℂ) * t (c x)) he

theorem stages_monotone
    (P : CompatibleModelData F ζ hζ)
    (L L' : Level F ζ hζ P) (h : L ≤ L')
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : Q = rationalModel F ζ hζ ∨ Q = productModel F ζ hζ P) :
    Stage F ζ hζ P L Q ≤ Stage F ζ hζ P L' Q := by
  have hK : L'.K ≤ L.K := h
  have hD : stageDomain F ζ hζ P L ≤ stageDomain F ζ hζ P L' := by
    intro x hx y hy
    exact hx y (hK hy)
  have hS : saturatedDomain F ζ hζ P L Q ⊆ saturatedDomain F ζ hζ P L' Q := by
    rintro g ⟨a, x, rfl⟩
    exact ⟨a, ⟨x.val, hD x.property⟩, rfl⟩
  intro f hf
  constructor
  · intro g hg
    exact hf.1 g (fun hmem => hg (hS hmem))
  · intro k x
    let k0 : phaseGroup F ζ hζ P L := ⟨k.val, hK k.property⟩
    have hkD : k.val ∈ stageDomain F ζ hζ P L :=
      phase_inside_domain F ζ hζ P L k0.property
    by_cases hx : x.val ∈ saturatedDomain F ζ hζ P L Q
    · obtain ⟨a, z, he⟩ := hx
      rw [he, mul_assoc, f.property a (z.val * k.val), f.property a z.val]
      rw [hf.2 k0 z]
      change (Q.character a : ℂ) * ((phaseCharacter F ζ hζ P L' k : ℂ) * f.val z.val) =
        (phaseCharacter F ζ hζ P L' k : ℂ) * ((Q.character a : ℂ) * f.val z.val)
      ring
    · have hxk : x.val * k.val ∉ saturatedDomain F ζ hζ P L Q := by
        rintro ⟨a, z, he⟩
        apply hx
        refine ⟨a, ⟨z.val * k.val⁻¹, (stageDomain F ζ hζ P L).mul_mem z.property
          ((stageDomain F ζ hζ P L).inv_mem hkD)⟩, ?_⟩
        have hh := congrArg (fun t => t * k.val⁻¹) he
        simpa [mul_assoc] using hh
      rw [hf.1 _ hxk, hf.1 _ hx, mul_zero]

 def rawPhaseStage (P : CompatibleModelData F ζ hζ)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) (K : Subgroup (D F)) :
    Submodule ℂ (KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q) where
  carrier := {f | (∀ g, (¬ ∃ (h : Q.H) (x : KPGlobalTorusFunctionData.E F ζ hζ),
        g = h.val * x ∧ ∀ k ∈ K,
          KPGlobalCubicIdelePairing.beta3 F ζ hζ
            (KPGlobalProductPolarizationCharacter.pD F ζ hζ x) k = 1) → f.val g = 0) ∧
      (∀ (k : B F ζ hζ P),
        KPGlobalProductPolarizationCharacter.pD F ζ hζ k.val ∈ K →
        ∀ (x : KPGlobalTorusFunctionData.E F ζ hζ),
          (∀ y ∈ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ
            (KPGlobalProductPolarizationCharacter.pD F ζ hζ x) y = 1) →
          f.val (x * k.val) =
            ((KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P.localData P.adjustment k /
              KPGlobalCenterRationalCharacter.positiveComplex
                (KPGlobalCenterRationalCharacter.nu F ζ hζ k.val) : ℂˣ) : ℂ) * f.val x)}
  zero_mem' := by constructor <;> intros <;> simp
  add_mem' := by
    intro f g hf hg
    constructor
    · intro x hx; simp [hf.1 x hx, hg.1 x hx]
    · intro k hk x hx; simp [hf.2 k hk x hx, hg.2 k hk x hx, mul_add]
  smul_mem' := by
    intro c f hf
    constructor
    · intro x hx; simp [hf.1 x hx]
    · intro k hk x hx
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hf.2 k hk x hx]
      ring

private theorem rawPhaseStage_eq (P : CompatibleModelData F ζ hζ)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) (L : Level F ζ hζ P) :
    rawPhaseStage F ζ hζ P Q L.K = Stage F ζ hζ P L Q := by
  ext f
  have hsat : ∀ g : E F ζ hζ,
      (∃ (h : Q.H) (x : E F ζ hζ), g = h.val * x ∧
        ∀ k ∈ L.K, KPGlobalCubicIdelePairing.beta3 F ζ hζ (pD F ζ hζ x) k = 1) ↔
      g ∈ saturatedDomain F ζ hζ P L Q := by
    intro g
    constructor
    · rintro ⟨h, x, he, hx⟩; exact ⟨h, ⟨x, hx⟩, he⟩
    · rintro ⟨h, x, he⟩; exact ⟨h, x.val, he, x.property⟩
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor
  · intro hf
    refine ⟨?_, ?_⟩
    · intro g hg; exact hf.1 g (fun h => hg ((hsat g).mp h))
    · intro k x
      exact hf.2 ⟨k.val, phase_inside_product F ζ hζ P L k.property⟩ k.property x.val x.property
  · intro hf
    refine ⟨?_, ?_⟩
    · intro g hg; exact hf.1 g (fun h => hg ((hsat g).mpr h))
    · intro k hk x hx
      exact hf.2 ⟨k.val, hk⟩ ⟨x, hx⟩

private theorem raw_model_formula (P : CompatibleModelData F ζ hζ)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : Q = rationalModel F ζ hζ ∨ Q = productModel F ζ hζ P) :
    (Q.H = R F ζ hζ ∧ ∀ (r : Q.H) (s : R F ζ hζ), r.val = s.val →
      Q.character r = KPGlobalCenterRationalCharacter.lambdaR F ζ hζ s /
        KPGlobalCenterRationalCharacter.positiveComplex
          (KPGlobalCenterRationalCharacter.nu F ζ hζ s.val)) ∨
    KPGlobalTorusTensorFibers.IsUnitProductModel F ζ hζ P.localData P.adjustment Q := by
  rcases hQ with rfl | rfl
  · left; refine ⟨rfl, ?_⟩
    intro r s h
    have he : r = s := Subtype.ext h
    subst s; rfl
  · right; refine ⟨rfl, ?_⟩
    intro r s h
    have he : r = s := Subtype.ext h
    subst s; rfl

theorem stage_in_smooth_level
    (P : CompatibleModelData F ζ hζ)
    (L : Level F ζ hζ P) (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : Q = rationalModel F ζ hζ ∨ Q = productModel F ζ hζ P) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      Stage F ζ hζ P L Q ≤ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U := by
  obtain ⟨U, hU⟩ := (KPGlobalTorusTensorFibers.scalar_phase_levels_cofinal
    F ζ hζ P.localData P.adjustment P.agrees Q (raw_model_formula F ζ hζ P Q hQ)
    (rawPhaseStage F ζ hζ P Q) (by intros; rfl)).1
      L.K L.inside L.compact L.open' L.transverse
  exact ⟨U, (rawPhaseStage_eq F ζ hζ P Q L) ▸ hU⟩

theorem smooth_level_in_stage
    (P : CompatibleModelData F ζ hζ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : Q = rationalModel F ζ hζ ∨ Q = productModel F ζ hζ P) :
    ∃ L : Level F ζ hζ P,
      KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U ≤ Stage F ζ hζ P L Q := by
  obtain ⟨K, hK, hc, ho, ht, hU⟩ := (KPGlobalTorusTensorFibers.scalar_phase_levels_cofinal
    F ζ hζ P.localData P.adjustment P.agrees Q (raw_model_formula F ζ hζ P Q hQ)
    (rawPhaseStage F ζ hζ P Q) (by intros; rfl)).2 U
  let L : Level F ζ hζ P := ⟨K, hK, hc, ho, ht⟩
  exact ⟨L, (rawPhaseStage_eq F ζ hζ P Q L) ▸ hU⟩

theorem stages_exhaust
    (P : CompatibleModelData F ζ hζ)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : Q = rationalModel F ζ hζ ∨ Q = productModel F ζ hζ P) :
    (⨆ L : Level F ζ hζ P, Stage F ζ hζ P L Q) =
      KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q := by
  apply le_antisymm
  · apply iSup_le
    intro L
    obtain ⟨U, hU⟩ := stage_in_smooth_level F ζ hζ P L Q hQ
    exact hU.trans (le_iSup (fun U => KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U) U)
  · apply iSup_le
    intro U
    obtain ⟨L, hL⟩ := smooth_level_in_stage F ζ hζ P U Q hQ
    exact hL.trans (le_iSup (fun L => Stage F ζ hζ P L Q) L)

theorem smooth_vector_in_stage
    (P : CompatibleModelData F ζ hζ)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : Q = rationalModel F ζ hζ ∨ Q = productModel F ζ hζ P)
    (f : KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q) :
    ∃ L : Level F ζ hζ P, f.val ∈ Stage F ζ hζ P L Q := by
  letI : Nonempty (Level F ζ hζ P) := levels_nonempty F ζ hζ P
  have hd : Directed (· ≤ ·) (fun L : Level F ζ hζ P => Stage F ζ hζ P L Q) := by
    intro L L'
    obtain ⟨L'', hL, hL'⟩ := levels_directed F ζ hζ P L L'
    exact ⟨L'', stages_monotone F ζ hζ P L L'' hL Q hQ,
      stages_monotone F ζ hζ P L' L'' hL' Q hQ⟩
  apply (Submodule.mem_iSup_of_directed _ hd).mp
  rw [stages_exhaust F ζ hζ P Q hQ]
  exact f.property

def stageTopology
    (P : CompatibleModelData F ζ hζ)
    (L : Level F ζ hζ P) (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hU : Stage F ζ hζ P L Q ≤ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U) :
    TopologicalSpace (Stage F ζ hζ P L Q) :=
  TopologicalSpace.induced (Submodule.inclusion hU)
    (KPGlobalTorusFunctionData.smoothLevelTopology Q.H Q.character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
      (KPGlobalTorusFunctionData.torusArchDomain F)
      (KPGlobalTorusFunctionData.torusArchDomain_open F)
      ((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype))

 abbrev levelJets (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    SeminormFamily ℂ (KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U)
      (E F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (KPGlobalTorusFunctionData.torusArchDomain F)) :=
  fun i : E F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (KPGlobalTorusFunctionData.torusArchDomain F) =>
    KPGlobalTorusFunctionData.jetSeminorm Q.H Q.character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
      (KPGlobalTorusFunctionData.torusArchDomain F)
      (KPGlobalTorusFunctionData.torusArchDomain_open F)
      ((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) i.1 i.2.1 i.2.2

set_option maxHeartbeats 1000000 in
private theorem stageJets_withSeminorms
    (P : CompatibleModelData F ζ hζ) (L : Level F ζ hζ P)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hU : Stage F ζ hζ P L Q ≤ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U) :
    @WithSeminorms ℂ (Stage F ζ hζ P L Q) _ _ _ _
      ((fun i => (levelJets F ζ hζ Q U i).comp (Submodule.inclusion hU)))
      (stageTopology F ζ hζ P L Q U hU) := by
  letI := KPGlobalTorusFunctionData.smoothLevelTopology Q.H Q.character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
      (KPGlobalTorusFunctionData.torusArchDomain F)
      (KPGlobalTorusFunctionData.torusArchDomain_open F)
      ((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
  have hp : WithSeminorms (levelJets F ζ hζ Q U) := ⟨rfl⟩
  have hh := LinearMap.withSeminorms_induced (E := Stage F ζ hζ P L Q)
    (σ₁₂ := RingHom.id ℂ) hp (Submodule.inclusion hU)
  exact hh

 abbrev smoothLevelTop (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :=
  KPGlobalTorusFunctionData.smoothLevelTopology Q.H Q.character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
      (KPGlobalTorusFunctionData.torusArchDomain F)
      (KPGlobalTorusFunctionData.torusArchDomain_open F)
      ((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)

 abbrev unionSeminorms (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) :=
  KPGlobalTorusFunctionData.finalSeminorms Q.H Q.character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
      (KPGlobalTorusFunctionData.torusArchDomain F)
      (KPGlobalTorusFunctionData.torusArchDomain_open F)
      (fun U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ =>
        (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
          (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)

set_option maxHeartbeats 1000000 in
private theorem smooth_to_stage_continuous
    (P : CompatibleModelData F ζ hζ) (L : Level F ζ hζ P)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (U W : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hU : KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U ≤ Stage F ζ hζ P L Q)
    (hW : Stage F ζ hζ P L Q ≤ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q W) :
    @Continuous _ _ (smoothLevelTop F ζ hζ Q U)
      (stageTopology F ζ hζ P L Q W hW) (Submodule.inclusion hU) := by
  letI := smoothLevelTop F ζ hζ Q U
  letI := stageTopology F ζ hζ P L Q W hW
  have hp : WithSeminorms (levelJets F ζ hζ Q U) := ⟨rfl⟩
  letI := hp.isTopologicalAddGroup
  have hq := stageJets_withSeminorms F ζ hζ P L Q W hW
  have hc := hq.continuous_of_continuous_comp (E := KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U)
    (τ₁₂ := RingHom.id ℂ) (Submodule.inclusion hU)
  apply hc
  intro i
  have he : ((levelJets F ζ hζ Q W i).comp (σ₁₂ := RingHom.id ℂ) (E := Stage F ζ hζ P L Q)
      (Submodule.inclusion hW)).comp (σ₁₂ := RingHom.id ℂ) (Submodule.inclusion hU) =
      levelJets F ζ hζ Q U i := by
    apply Seminorm.ext
    intro f
    rfl
  rw [he]
  exact hp.continuous_seminorm i

set_option maxHeartbeats 1000000 in
private theorem stage_to_union_continuous
    (P : CompatibleModelData F ζ hζ) (L : Level F ζ hζ P)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hU : Stage F ζ hζ P L Q ≤ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U) :
    @Continuous _ _ (stageTopology F ζ hζ P L Q U hU)
      (KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ Q)
      (Submodule.inclusion (hU.trans (le_iSup (fun W =>
        KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q W) U))) := by
  have hc := KPGlobalTorusFunctionData.stageInclusion_continuous Q.H Q.character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
      (KPGlobalTorusFunctionData.torusArchDomain F)
      (KPGlobalTorusFunctionData.torusArchDomain_open F)
      (fun U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ =>
        (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
          (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) U
  letI := smoothLevelTop F ζ hζ Q U
  letI := stageTopology F ζ hζ P L Q U hU
  letI := KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ Q
  have hd : Continuous (Submodule.inclusion hU) := continuous_induced_dom
  exact hc.comp hd

set_option maxHeartbeats 1000000 in

theorem levelwise_final_topology
    (P : CompatibleModelData F ζ hζ)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : Q = rationalModel F ζ hζ ∨ Q = productModel F ζ hζ P)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [Module ℝ V] [IsScalarTower ℝ ℂ V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [ContinuousSMul ℝ V]
    [LocallyConvexSpace ℝ V]
    (T : KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q →ₗ[ℂ] V) :
    @Continuous _ _ (KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ Q)
      inferInstance T ↔
    ∀ (L : Level F ζ hζ P) (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
      (hU : Stage F ζ hζ P L Q ≤ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U),
      @Continuous _ _ (stageTopology F ζ hζ P L Q U hU) inferInstance
        (T.comp (Submodule.inclusion
          (hU.trans (le_iSup (fun W : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ =>
            KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q W) U)))) := by
  letI := KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ Q
  have hp : WithSeminorms (fun q : unionSeminorms F ζ hζ Q => q.val) := ⟨rfl⟩
  letI := hp.isTopologicalAddGroup
  letI : LocallyConvexSpace ℂ V := LocallyConvexSpace.ofBasisZero ℂ V _ _
    (LocallyConvexSpace.convex_basis_zero ℝ V)
    (fun s hs => convex_RCLike_iff_convex_real.mpr hs.2)
  constructor
  · intro h L U hU
    letI := stageTopology F ζ hζ P L Q U hU
    exact h.comp (stage_to_union_continuous F ζ hζ P L Q U hU)
  · intro h
    have ht := (PolynormableSpace.withSeminorms ℂ V).continuous_of_continuous_comp
      (E := KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q) (τ₁₂ := RingHom.id ℂ) T
    apply ht
    intro q
    have hlevels : ∀ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
        @Continuous (KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U) ℝ
          (smoothLevelTop F ζ hζ Q U) inferInstance
          ((q.val.comp T) ∘ Submodule.inclusion
            (le_iSup (fun W => KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q W) U)) := by
      intro U
      obtain ⟨L, hL⟩ := smooth_level_in_stage F ζ hζ P U Q hQ
      obtain ⟨W, hW⟩ := stage_in_smooth_level F ζ hζ P L Q hQ
      letI := stageTopology F ζ hζ P L Q W hW
      letI := smoothLevelTop F ζ hζ Q U
      have hc := (q.property.comp (h L W hW)).comp
        (smooth_to_stage_continuous F ζ hζ P L Q U W hL hW)
      exact hc
    let p : unionSeminorms F ζ hζ Q := ⟨q.val.comp T, hlevels⟩
    exact hp.continuous_seminorm p

structure LocalFiberData (P : CompatibleModelData F ζ hζ) where
  canonical : ∀ q : HeightOneSpectrum (𝓞 F),
    KPLocalExceptionalConstruction.CanonicalFiniteInducingData F ζ hζ q
  polarization : ∀ q, KPLocalStoneVonNeumann.Polarization (canonical q).heisenberg
  subgroup_matches : ∀ q,
    ((polarization q).L.comap (canonical q).heisenberg.π).map
      (KPLocalExceptionalConstruction.actualTorus F ζ hζ q).subtype =
    (KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q)
      (P.localData.localData (Sum.inr q)).L).map
      (KPGlobalProductPolarizationCharacter.localTorus F ζ hζ (Sum.inr q)).subtype
  character_matches : ∀ q
    (a : (polarization q).L.comap (canonical q).heisenberg.π)
    (b : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q)
      (P.localData.localData (Sum.inr q)).L),
    a.val.val = b.val.val → (polarization q).ωL a =
      KPGlobalProductPolarizationCharacter.adjustedLocalValue F ζ hζ
        P.localData P.adjustment (Sum.inr q) b
  exceptional : Finset (HeightOneSpectrum (𝓞 F))
  unramified : ∀ q, q ∉ exceptional →
    KPLocalGoodSphericalImage.UnramifiedCompactInducingData
      (canonical q).borel (polarization q) (canonical q).iwasawa
  actual_compact : ∀ q, q ∉ exceptional →
    ∃ ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3,
      ((canonical q).iwasawa.compact.toOpenSubgroup :
        Subgroup (KPLocalExceptionalConstruction.ActualCover F ζ hζ q)) =
      (KPLocalExceptionalConstruction.actualGoodCompactSplit F ζ hζ q ht).range

abbrev LocalFiber (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)
    (q : HeightOneSpectrum (𝓞 F)) :=
  ↥(KPLocalStoneVonNeumann.InducedModule (C.polarization q))

abbrev localTau (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)
    (q : HeightOneSpectrum (𝓞 F)) := KPLocalStoneVonNeumann.tau (C.polarization q)

def localReference (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)
    (q : HeightOneSpectrum (𝓞 F)) : LocalFiber F ζ hζ P C q :=
  ⟨fun t => if h : (C.canonical q).heisenberg.π t ∈ (C.polarization q).L then
    ((C.polarization q).ωL ⟨t, h⟩ : ℂ) else 0, by
    intro a x
    by_cases hx : (C.canonical q).heisenberg.π x ∈ (C.polarization q).L
    · have hax : (C.canonical q).heisenberg.π (a.val * x) ∈ (C.polarization q).L := by
        rw [map_mul]
        exact (C.polarization q).L.mul_mem a.property hx
      simp only [dif_pos hx, dif_pos hax]
      exact congrArg (fun u : ℂˣ => (u : ℂ)) ((C.polarization q).ωL.map_mul a ⟨x, hx⟩)
    · have hax : (C.canonical q).heisenberg.π (a.val * x) ∉ (C.polarization q).L := by
        rw [map_mul, (C.polarization q).L.mul_mem_cancel_left a.property]
        exact hx
      simp only [dif_neg hx, dif_neg hax, mul_zero]⟩

theorem referenceGoodSpherical (P : CompatibleModelData F ζ hζ)
    (C : LocalFiberData F ζ hζ P) (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ C.exceptional) :
    localReference F ζ hζ P C q ∈ fixedSubmodule (localTau F ζ hζ P C q)
      (KPLocalGoodSphericalImage.compactTorus (C.canonical q).borel (C.canonical q).iwasawa) ∧
    (localReference F ζ hζ P C q).val 1 = 1 ∧
    ∀ v : LocalFiber F ζ hζ P C q,
      v ∈ fixedSubmodule (localTau F ζ hζ P C q)
        (KPLocalGoodSphericalImage.compactTorus (C.canonical q).borel (C.canonical q).iwasawa) →
      v.val 1 = 1 → v = localReference F ζ hζ P C q := by
  have hu := C.unramified q hq
  have hfixed : localReference F ζ hζ P C q ∈ fixedSubmodule (localTau F ζ hζ P C q)
      (KPLocalGoodSphericalImage.compactTorus (C.canonical q).borel (C.canonical q).iwasawa) := by
    intro j
    apply Subtype.ext
    funext x
    change (localReference F ζ hζ P C q).val (x * j.val) =
      (localReference F ζ hζ P C q).val x
    have hj : (C.canonical q).heisenberg.π j.val ∈ (C.polarization q).L := by
      rw [← hu.polarization_image]
      exact Subgroup.mem_map.mpr ⟨j, j.property, rfl⟩
    by_cases hx : (C.canonical q).heisenberg.π x ∈ (C.polarization q).L
    · have hxj : (C.canonical q).heisenberg.π (x * j.val) ∈ (C.polarization q).L := by
        rw [map_mul]; exact (C.polarization q).L.mul_mem hx hj
      simp only [localReference, dif_pos hx, dif_pos hxj]
      have hh := (C.polarization q).ωL.map_mul ⟨x, hx⟩ ⟨j, hj⟩
      change (C.polarization q).ωL ⟨x * j.val, hxj⟩ =
        (C.polarization q).ωL ⟨x, hx⟩ * (C.polarization q).ωL ⟨j, hj⟩ at hh
      rw [hh, hu.character_trivial j hj, mul_one]
    · have hxj : (C.canonical q).heisenberg.π (x * j.val) ∉ (C.polarization q).L := by
        rw [map_mul, (C.polarization q).L.mul_mem_cancel_right hj]; exact hx
      simp only [localReference, dif_neg hx, dif_neg hxj]
  have hone : (localReference F ζ hζ P C q).val 1 = 1 := by
    simp only [localReference, map_one]
    simp only [Subgroup.one_mem, dite_true]
    change (((C.polarization q).ωL 1 : ℂˣ) : ℂ) = 1
    rw [map_one, Units.val_one]
  refine ⟨hfixed, hone, ?_⟩
  obtain ⟨w, hw, huniq⟩ := KPLocalGoodSphericalImage.normalized_inducing_vector
    (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa hu
  intro v hv hn
  exact (huniq v ⟨hv, hn⟩).trans (huniq (localReference F ζ hζ P C q) ⟨hfixed, hone⟩).symm

def localUntwistedEvaluation (P : CompatibleModelData F ζ hζ)
    (C : LocalFiberData F ζ hζ P) (q : HeightOneSpectrum (𝓞 F))
    (f : LocalFiber F ζ hζ P C q)
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) : ℂ :=
  f.val t / (Real.rpow
    (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate t)) (1 / 6 : ℝ) : ℂ)

 def rawLocalScalarData (P : CompatibleModelData F ζ hζ)
    (C : LocalFiberData F ζ hζ P) :
    KPGlobalTorusTensorFibers.RawLocalScalarData F ζ hζ P.localData P.adjustment where
  canonical := C.canonical
  polarization := C.polarization
  subgroup_matches := C.subgroup_matches
  character_matches := C.character_matches
  exceptional := C.exceptional
  unramified := C.unramified
  actual_compact := C.actual_compact
  reference := localReference F ζ hζ P C
  reference_formula := by intros; rfl
  evaluation := localUntwistedEvaluation F ζ hζ P C
  evaluation_formula := by intros; rfl

private theorem product_model_raw (P : CompatibleModelData F ζ hζ) :
    KPGlobalTorusTensorFibers.IsUnitProductModel F ζ hζ
      P.localData P.adjustment (productModel F ζ hζ P) := by
  refine ⟨rfl, ?_⟩
  intro r s h
  have he : r = s := Subtype.ext h
  subst s
  rfl

theorem local_evaluation_finiteSupport (P : CompatibleModelData F ζ hζ)
    (C : LocalFiberData F ζ hζ P)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (f : ∀ q : S, LocalFiber F ζ hζ P C q)
    (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (ht : ∀ q, (t q).val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) :
    Function.HasFiniteMulSupport (fun q => localUntwistedEvaluation F ζ hζ P C q
      (if h : q ∈ S then f ⟨q, h⟩ else localReference F ζ hζ P C q) (t q)) := by
  exact KPGlobalTorusTensorFibers.restricted_local_evaluations_finite_support
    F ζ hζ P.localData P.adjustment (rawLocalScalarData F ζ hζ P C) S hS f raw t ht

abbrev TensorStage (P : CompatibleModelData F ζ hζ)
    (C : LocalFiberData F ζ hζ P) (S : Finset (HeightOneSpectrum (𝓞 F))) :=
  RestrictedTensorSimple.Stage (LocalFiber F ζ hζ P C) S

theorem finite_tensor_realization_exists (P : CompatibleModelData F ζ hζ)
    (C : LocalFiberData F ζ hζ P)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S) :
    ∃ T : TensorStage F ζ hζ P C S →ₗ[ℂ]
        KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ (productModel F ζ hζ P),
      ∀ (f : ∀ q : S, LocalFiber F ζ hζ P C q)
        (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
        (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
        (g : E F ζ hζ),
        (∀ w : InfinitePlace F, raw (Sum.inl w) = 1) →
        (∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) →
        KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = g.val →
        (T (PiTensorProduct.tprod ℂ f)).val.val g =
          ∏ᶠ q, localUntwistedEvaluation F ζ hζ P C q
            (if h : q ∈ S then f ⟨q, h⟩ else localReference F ζ hζ P C q) (t q) := by
  exact KPGlobalTorusTensorFibers.raw_finite_tensor_realization_exists
    F ζ hζ P.localData P.adjustment (rawLocalScalarData F ζ hζ P C)
    (productModel F ζ hζ P) (product_model_raw F ζ hζ P) S hS

def finiteTensorRealization (P : CompatibleModelData F ζ hζ)
    (C : LocalFiberData F ζ hζ P)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S) :=
  Classical.choose (finite_tensor_realization_exists F ζ hζ P C S hS)

theorem finiteTensorRealization_formula (P : CompatibleModelData F ζ hζ)
    (C : LocalFiberData F ζ hζ P)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S) :
    ∀ (f : ∀ q : S, LocalFiber F ζ hζ P C q)
        (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
        (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
        (g : E F ζ hζ),
        (∀ w : InfinitePlace F, raw (Sum.inl w) = 1) →
        (∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) →
        KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = g.val →
        (finiteTensorRealization F ζ hζ P C S hS (PiTensorProduct.tprod ℂ f)).val.val g =
          ∏ᶠ q, localUntwistedEvaluation F ζ hζ P C q
            (if h : q ∈ S then f ⟨q, h⟩ else localReference F ζ hζ P C q) (t q) :=
  Classical.choose_spec (finite_tensor_realization_exists F ζ hζ P C S hS)

theorem tensor_insertion_compatible (P : CompatibleModelData F ζ hζ)
    (C : LocalFiberData F ζ hζ P)
    (S T : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S) (hST : S ⊆ T) :
    (finiteTensorRealization F ζ hζ P C T (hS.trans hST)).comp
      (RestrictedTensorSimple.insert (LocalFiber F ζ hζ P C)
        (localReference F ζ hζ P C) S T hST) =
      finiteTensorRealization F ζ hζ P C S hS := by
  exact (KPGlobalTorusTensorFibers.raw_tensor_family_identification
    F ζ hζ P.localData P.adjustment (rawLocalScalarData F ζ hζ P C)
    (productModel F ζ hζ P) (product_model_raw F ζ hζ P)
    (finiteTensorRealization F ζ hζ P C)
    (finiteTensorRealization_formula F ζ hζ P C)).2.2 S T hS hST

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStages

section

open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStages
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem characters_agree (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)
    (hT : ∀ (b : B F ζ hζ P) (r : R F ζ hζ), b.val = r.val →
      KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T b =
        KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r)
    (r : R F ζ hζ) (b : B F ζ hζ P) (h : r.val = b.val) :
    rationalUnitCharacter F ζ hζ r = productUnitCharacter F ζ hζ P T b := by
  change rationalUnitValue F ζ hζ r = productUnitValue F ζ hζ P T b
  unfold rationalUnitValue productUnitValue
  rw [hT b r h.symm, h]

private theorem beta_swap (x y : D F) :
    KPGlobalCubicIdelePairing.beta3 F ζ hζ x y *
      KPGlobalCubicIdelePairing.beta3 F ζ hζ y x = 1 := by
  have hb := KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ
  have hh := hb.2.2 (x * y)
  rw [hb.1, hb.2.1, hb.2.1, hb.2.2, hb.2.2] at hh
  simpa using hh

private theorem beta_quotient_congr
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) (x y x' y' : annihilator F ζ hζ L.K)
    (hx : quotientClass F ζ hζ P L x = quotientClass F ζ hζ P L x')
    (hy : quotientClass F ζ hζ P L y = quotientClass F ζ hζ P L y') :
    KPGlobalCubicIdelePairing.beta3 F ζ hζ x.val y.val =
      KPGlobalCubicIdelePairing.beta3 F ζ hζ x'.val y'.val := by
  obtain ⟨k, hk, he⟩ := (QuotientGroup.mk'_eq_mk' _).mp hx
  obtain ⟨l, hl, hf⟩ := (QuotientGroup.mk'_eq_mk' _).mp hy
  rw [← he, ← hf]
  change KPGlobalCubicIdelePairing.beta3 F ζ hζ x.val y.val =
    KPGlobalCubicIdelePairing.beta3 F ζ hζ (x.val * k.val) (y.val * l.val)
  have hb := KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ
  have hky : KPGlobalCubicIdelePairing.beta3 F ζ hζ k.val y.val = 1 := by
    have hs := beta_swap F ζ hζ k.val y.val
    rw [y.property k.val hk, mul_one] at hs
    exact hs
  rw [hb.1, hb.2.1, hb.2.1, x.property l.val hl, hky,
    k.property l.val hl]
  simp

theorem exists_stage_pairing
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) :
    ∃ β : symplecticQuotient F ζ hζ P L →
        symplecticQuotient F ζ hζ P L → rootsOfUnity 3 F,
      ∀ x y : annihilator F ζ hζ L.K,
        β (quotientClass F ζ hζ P L x) (quotientClass F ζ hζ P L y) =
          KPGlobalCubicIdelePairing.beta3 F ζ hζ x.val y.val := by
  refine ⟨Quotient.lift₂
    (fun x y : annihilator F ζ hζ L.K => KPGlobalCubicIdelePairing.beta3 F ζ hζ x.val y.val)
    ?_, ?_⟩
  · intro x y x' y' hx hy
    exact beta_quotient_congr F ζ hζ P L x y x' y'
      (Quotient.sound hx) (Quotient.sound hy)
  · intro x y
    rfl

def stagePairing (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) : symplecticQuotient F ζ hζ P L →
        symplecticQuotient F ζ hζ P L → rootsOfUnity 3 F :=
  Classical.choose (exists_stage_pairing F ζ hζ P L)

theorem stagePairing_formula (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) (x y : annihilator F ζ hζ L.K) :
    stagePairing F ζ hζ P L (quotientClass F ζ hζ P L x)
      (quotientClass F ζ hζ P L y) = KPGlobalCubicIdelePairing.beta3 F ζ hζ x.val y.val :=
  (Classical.choose_spec (exists_stage_pairing F ζ hζ P L)) x y

private theorem class_cube (x : D F) : x ^ 3 = 1 := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    change (QuotientGroup.mk' (CubicCharacters.cubes (KPGlobalCubicIdelePairing.Ideles F)) x) ^ 3 = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩

private theorem compact_double_annihilator (K : Subgroup (D F))
    (hK : IsCompact (K : Set (D F))) (x : D F)
    (hx : ∀ y ∈ annihilator F ζ hζ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ x y = 1) :
    x ∈ K := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  by_contra hn
  let U : D F → Set (D F) := fun y =>
    {k | KPGlobalCubicIdelePairing.beta3 F ζ hζ k y ≠ KPGlobalCubicIdelePairing.beta3 F ζ hζ x y}
  have hU : ∀ y, IsOpen (U y) := by
    intro y
    exact (isOpen_discrete ({KPGlobalCubicIdelePairing.beta3 F ζ hζ x y}ᶜ)).preimage
      ((KPGlobalCubicIdelePairing.beta3_continuous F ζ hζ).comp
        (continuous_id.prodMk continuous_const))
  have hcover : (K : Set (D F)) ⊆ ⋃ y, U y := by
    intro k hk
    apply Set.mem_iUnion.mpr
    by_contra hh
    have he : ∀ y, KPGlobalCubicIdelePairing.beta3 F ζ hζ k y =
        KPGlobalCubicIdelePairing.beta3 F ζ hζ x y := by
      simpa only [not_exists, U, Set.mem_setOf_eq, not_not] using hh
    have hzero : k / x = 1 := by
      apply (KPGlobalCubicIdelePairing.beta3_radical_zero F ζ hζ _).mp
      intro y
      change betaLeft F ζ hζ y (k / x) = 1
      rw [map_div]
      change KPGlobalCubicIdelePairing.beta3 F ζ hζ k y /
        KPGlobalCubicIdelePairing.beta3 F ζ hζ x y = 1
      rw [he, div_self']
    exact hn ((div_eq_one.mp hzero) ▸ hk)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU hcover
  let Y := Subgroup.closure (s : Set (D F))
  have hpow : ∀ y : Y, y ^ 3 = 1 := by
    intro y
    apply Subtype.ext
    exact class_cube F y.val
  letI : Finite Y := CommGroup.finite_of_fg_isMulTorsion Y
    (fun y => isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hpow y⟩)
  letI : HasEnoughRootsOfUnity F 3 :=
    { prim := ⟨ζ ^ 4, hζ.pow (by norm_num : 0 < 12) (by norm_num : 12 = 4 * 3)⟩
      cyc := inferInstance }
  letI : HasEnoughRootsOfUnity F (Monoid.exponent Y) :=
    HasEnoughRootsOfUnity.of_dvd F (Monoid.exponent_dvd_of_forall_pow_eq_one hpow)
  let eval : D F →* (Y →* Fˣ) :=
    { toFun := fun k => (rootsOfUnity 3 F).subtype.comp ((betaRight F ζ hζ k).comp Y.subtype)
      map_one' := by
        apply MonoidHom.ext
        intro y
        exact congrArg Subtype.val ((betaLeft F ζ hζ y.val).map_one)
      map_mul' := by
        intro k l
        apply MonoidHom.ext
        intro y
        exact congrArg Subtype.val ((KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1 k l y.val) }
  letI : HasEnoughRootsOfUnity F (Monoid.exponent (Y →* Fˣ)) := by
    apply HasEnoughRootsOfUnity.of_dvd F (n := 3)
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro φ
    apply MonoidHom.ext
    intro y
    change φ y ^ 3 = 1
    rw [← map_pow, hpow, map_one]
  let H := K.map eval
  have hmember : eval x ∈ H := by
    apply (CommGroup.forall_monoidHom_apply_eq_one_iff F H (eval x)).mp
    intro φ hφ
    let y := CommGroup.monoidHomMonoidHomEquiv Y F φ
    have hy : y.val ∈ annihilator F ζ hζ K := by
      intro k hk
      apply beta_symmetric_one F ζ hζ
      apply Subtype.ext
      change (eval k) y = 1
      rw [CommGroup.apply_monoidHomMonoidHomEquiv]
      exact hφ (eval k) (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
    have hxy := hx y.val hy
    have he := congrArg Subtype.val hxy
    change (eval x) y = 1 at he
    rw [CommGroup.apply_monoidHomMonoidHomEquiv] at he
    exact he
  obtain ⟨k, hk, he⟩ := Subgroup.mem_map.mp hmember
  obtain ⟨y, hyS, hky⟩ := Set.mem_iUnion₂.mp (hs hk)
  let y' : Y := ⟨y, Subgroup.subset_closure hyS⟩
  have hval := congrArg (fun f : Y →* Fˣ => f y') he
  apply hky
  exact Subtype.ext hval

theorem finite_symplectic (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) :
    (∀ x y z, stagePairing F ζ hζ P L (x * y) z =
        stagePairing F ζ hζ P L x z * stagePairing F ζ hζ P L y z) ∧
    (∀ x y z, stagePairing F ζ hζ P L x (y * z) =
        stagePairing F ζ hζ P L x y * stagePairing F ζ hζ P L x z) ∧
    (∀ x, stagePairing F ζ hζ P L x x = 1) ∧
    (∀ x, (∀ y, stagePairing F ζ hζ P L x y = 1) → x = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y z
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        induction z using QuotientGroup.induction_on with
        | H z =>
          change stagePairing F ζ hζ P L (quotientClass F ζ hζ P L (x * y))
            (quotientClass F ζ hζ P L z) =
              stagePairing F ζ hζ P L (quotientClass F ζ hζ P L x) (quotientClass F ζ hζ P L z) *
              stagePairing F ζ hζ P L (quotientClass F ζ hζ P L y) (quotientClass F ζ hζ P L z)
          simp only [stagePairing_formula]
          exact (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1 x.val y.val z.val
  · intro x y z
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        induction z using QuotientGroup.induction_on with
        | H z =>
          change stagePairing F ζ hζ P L (quotientClass F ζ hζ P L x)
            (quotientClass F ζ hζ P L (y * z)) =
              stagePairing F ζ hζ P L (quotientClass F ζ hζ P L x) (quotientClass F ζ hζ P L y) *
              stagePairing F ζ hζ P L (quotientClass F ζ hζ P L x) (quotientClass F ζ hζ P L z)
          simp only [stagePairing_formula]
          exact (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).2.1 x.val y.val z.val
  · intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      change stagePairing F ζ hζ P L (quotientClass F ζ hζ P L x)
        (quotientClass F ζ hζ P L x) = 1
      rw [stagePairing_formula]
      exact (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).2.2 x.val
  · intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      intro hx
      apply (QuotientGroup.eq_one_iff x).mpr
      apply compact_double_annihilator F ζ hζ L.K L.compact x.val
      intro y hy
      have he := hx (quotientClass F ζ hζ P L ⟨y, hy⟩)
      change stagePairing F ζ hζ P L (quotientClass F ζ hζ P L x)
        (quotientClass F ζ hζ P L ⟨y, hy⟩) = 1 at he
      rw [stagePairing_formula] at he
      exact he

def rationalPolarization (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) : Subgroup (symplecticQuotient F ζ hζ P L) :=
  ((A F ⊓ annihilator F ζ hζ L.K).comap
    (annihilator F ζ hζ L.K).subtype).map (QuotientGroup.mk' _)

def productPolarization (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) : Subgroup (symplecticQuotient F ζ hζ P L) :=
  ((M F ζ hζ P).comap (annihilator F ζ hζ L.K).subtype).map (QuotientGroup.mk' _)

theorem rational_maximal_isotropic
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) :
    KPGlobalProductPolarizationCharacter.IsMaximalIsotropic F
      (stagePairing F ζ hζ P L) (rationalPolarization F ζ hζ P L) := by
  constructor
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    change stagePairing F ζ hζ P L (quotientClass F ζ hζ P L a)
      (quotientClass F ζ hζ P L b) = 1
    rw [stagePairing_formula]
    have hself := KPGlobalPrincipalCubicLagrangian.principal_self_annihilating F ζ hζ
    have horth : a.val ∈ KPGlobalPrincipalCubicLagrangian.annihilator F ζ hζ (A F) := by
      rw [hself]
      exact ha.1
    exact horth b.val hb.1
  · intro N hN hi
    apply le_antisymm _ hN
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨a, ha, hak, k, hk, he⟩ :=
        (KPGlobalTorusTensorFibers.rational_compact_open_annihilator
          F ζ hζ L.K L.compact L.open'
          (fun x hx y hy => level_isotropic F ζ hζ P L hx y hy)) x.val x.property (by
            intro a ha hak
            let aa : annihilator F ζ hζ L.K := ⟨a, hak⟩
            have hh := hi (quotientClass F ζ hζ P L x) hx
              (quotientClass F ζ hζ P L aa)
              (hN (Subgroup.mem_map.mpr ⟨aa, ⟨ha, hak⟩, rfl⟩))
            exact (stagePairing_formula F ζ hζ P L x aa).symm.trans hh)
      apply Subgroup.mem_map.mpr
      refine ⟨⟨a, hak⟩, ⟨ha, hak⟩, ?_⟩
      apply (QuotientGroup.eq).mpr
      change a⁻¹ * x.val ∈ L.K
      rw [he, inv_mul_cancel_left]
      exact hk

theorem product_maximal_isotropic
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (L : Level F ζ hζ P) :
    KPGlobalProductPolarizationCharacter.IsMaximalIsotropic F
      (stagePairing F ζ hζ P L) (productPolarization F ζ hζ P L) := by
  let β := stagePairing F ζ hζ P L
  let π := QuotientGroup.mk' (L.K.comap (annihilator F ζ hζ L.K).subtype)
  constructor
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    change stagePairing F ζ hζ P L (quotientClass F ζ hζ P L a)
      (quotientClass F ζ hζ P L b) = 1
    rw [stagePairing_formula]
    exact (KPGlobalProductPolarizationCharacter.M_maximal_isotropic F ζ hζ P).1
      a.val ha b.val hb
  · intro N hN hi
    let H := (N.comap π).map (annihilator F ζ hζ L.K).subtype
    have hMH : M F ζ hζ P ≤ H := by
      intro m hm
      let a : annihilator F ζ hζ L.K := ⟨m, product_inside_annihilator F ζ hζ P L hm⟩
      exact Subgroup.mem_map.mpr ⟨a, hN (Subgroup.mem_map.mpr ⟨a, hm, rfl⟩), rfl⟩
    have hHI : ∀ x ∈ H, ∀ y ∈ H, KPGlobalCubicIdelePairing.beta3 F ζ hζ x y = 1 := by
      intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
      change KPGlobalCubicIdelePairing.beta3 F ζ hζ a.val b.val = 1
      rw [← stagePairing_formula F ζ hζ P L a b]
      exact hi (π a) ha (π b) hb
    have hH : H = M F ζ hζ P :=
      (KPGlobalProductPolarizationCharacter.M_maximal_isotropic F ζ hζ P).2 H hMH hHI
    apply le_antisymm _ hN
    intro z hz
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (L.K.comap (annihilator F ζ hζ L.K).subtype) z
    have ha : a.val ∈ H := Subgroup.mem_map.mpr ⟨a, hz, rfl⟩
    rw [hH] at ha
    exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩

theorem compatibleModelData_exists
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ) :
    ∃ C : CompatibleModelData F ζ hζ, C.localData = P := by
  obtain ⟨T, hT⟩ := KPGlobalProductPolarizationCharacter.exists_finite_compatible_adjustment F ζ hζ P
  exact ⟨⟨P, T, hT⟩, rfl⟩

theorem compatibleAdjustment_agrees
    (P : CompatibleModelData F ζ hζ)
    (b : B F ζ hζ P) (r : R F ζ hζ) (h : b.val = r.val) :
    productUnitCharacter F ζ hζ P (compatibleAdjustment F ζ hζ P) b =
      rationalUnitCharacter F ζ hζ r := by
  exact (characters_agree F ζ hζ P P.adjustment P.agrees r b h.symm).symm

private theorem ordinaryPGLMap_injective (q : HeightOneSpectrum (𝓞 F)) :
    Function.Injective (KPLocalSmoothRepresentation.ordinaryPGLMap F q) := by
  letI : (KPPGLLocalCover.scalarSubgroup F (Sum.inr q)).Normal :=
    KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
  apply (injective_iff_map_eq_one _).mpr
  intro g
  induction g using QuotientGroup.induction_on with
  | H A =>
    intro h
    have hA : A ∈ Subgroup.center (KPRankOneInduction.GL2 F q) :=
      (QuotientGroup.eq_one_iff A).mp h
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hA
    obtain ⟨u, hu⟩ := hA
    apply (QuotientGroup.eq_one_iff A).mpr
    exact ⟨u, hu⟩

private theorem diagonal_matrix_normalize (q : HeightOneSpectrum (𝓞 F))
    (A : KPRankOneInduction.GL2 F q) (h10 : A 1 0 = 0) (h01 : A 0 1 = 0) :
    ∃ y : (q.adicCompletion F)ˣ, Matrix.ProjGenLinGroup.mk A =
      Matrix.ProjGenLinGroup.mk (KPGlobalProductPolarizationCharacter.diagonalHom F (Sum.inr q) y) := by
  have hprod : A 0 0 * A 1 1 ≠ 0 := by
    simpa [Matrix.det_fin_two, h10, h01] using Matrix.GeneralLinearGroup.det_ne_zero A
  have h00 := (mul_ne_zero_iff.mp hprod).1
  have h11 := (mul_ne_zero_iff.mp hprod).2
  let a : (q.adicCompletion F)ˣ := Units.mk0 (A 0 0) h00
  let d : (q.adicCompletion F)ˣ := Units.mk0 (A 1 1) h11
  refine ⟨a / d, ?_⟩
  have he : A = KPGlobalProductPolarizationCharacter.diagonalHom F (Sum.inr q) (a / d) *
      Matrix.GeneralLinearGroup.scalar (Fin 2) d := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [KPGlobalProductPolarizationCharacter.diagonalHom, KubotaRankTwo.d,
        Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
        a, d, h10, h01, h11]
  rw [he, map_mul]
  have hs : Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) d) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨d, rfl⟩
  rw [hs, mul_one]

theorem actual_local_torus_eq (q : HeightOneSpectrum (𝓞 F)) :
    KPLocalExceptionalConstruction.actualTorus F ζ hζ q =
      KPGlobalProductPolarizationCharacter.localTorus F ζ hζ (Sum.inr q) := by
  ext t
  change KPLocalSmoothRepresentation.ordinaryPGLMap F q
      (KPPGLLocalCover.projection F ζ hζ (Sum.inr q) t) ∈ KPRankOneInduction.diagonalTorus F q ↔
    KPPGLLocalCover.projection F ζ hζ (Sum.inr q) t ∈
      KPGlobalProductPolarizationCharacter.localOrdinaryTorus F (Sum.inr q)
  constructor
  · rintro ⟨A, hA, h10, h01⟩
    obtain ⟨y, hy⟩ := diagonal_matrix_normalize F q A h10 h01
    refine ⟨y, ?_⟩
    apply ordinaryPGLMap_injective F q
    exact hy.symm.trans hA
  · rintro ⟨y, hy⟩
    refine ⟨KPGlobalProductPolarizationCharacter.diagonalHom F (Sum.inr q) y, ?_, ?_, ?_⟩
    · exact congrArg (KPLocalSmoothRepresentation.ordinaryPGLMap F q) hy
    · simp [KPGlobalProductPolarizationCharacter.diagonalHom, KubotaRankTwo.d]
    · simp [KPGlobalProductPolarizationCharacter.diagonalHom, KubotaRankTwo.d]

theorem finiteTensorRealization_injective (P : CompatibleModelData F ζ hζ)
    (C : LocalFiberData F ζ hζ P)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S) :
    Function.Injective (finiteTensorRealization F ζ hζ P C S hS) := by
  exact (KPGlobalTorusTensorFibers.raw_tensor_family_identification
    F ζ hζ P.localData P.adjustment (rawLocalScalarData F ζ hζ P C)
    (productModel F ζ hζ P) (product_model_raw F ζ hζ P)
    (finiteTensorRealization F ζ hζ P C)
    (finiteTensorRealization_formula F ζ hζ P C)).1 S hS

theorem product_core_finite_modifications (P : CompatibleModelData F ζ hζ)
    (C : LocalFiberData F ζ hζ P)
    (f : KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ (productModel F ζ hζ P)) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
      (x : TensorStage F ζ hζ P C S), finiteTensorRealization F ζ hζ P C S hS x = f := by
  exact (KPGlobalTorusTensorFibers.raw_tensor_family_identification
    F ζ hζ P.localData P.adjustment (rawLocalScalarData F ζ hζ P C)
    (productModel F ζ hζ P) (product_model_raw F ζ hζ P)
    (finiteTensorRealization F ζ hζ P C)
    (finiteTensorRealization_formula F ζ hζ P C)).2.1 f

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStages

end
