module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteClassProjection
public import DedekindZetaZeroFree.Metaplectic.Torus.ArchimedeanChartCharacter

@[expose] public section

section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def pairingHom : KPGlobalCubicIdelePairing.D F →*
    KPGlobalCubicIdelePairing.D F →* Fˣ :=
  MonoidHom.mk' (fun x => MonoidHom.mk'
    (fun y => (KPGlobalCubicIdelePairing.beta3 F ζ hζ x y).val)
    (fun y z => congrArg Subtype.val
      ((KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).2.1 x y z)))
    (fun x y => MonoidHom.ext (fun z => congrArg Subtype.val
      ((KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1 x y z)))

private theorem finite_matching
    (S K : Subgroup (KPGlobalCubicIdelePairing.D F))
    (x : KPGlobalCubicIdelePairing.D F)
    (hx : ∀ a ∈ S,
      (∀ k ∈ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ a k = 1) →
      KPGlobalCubicIdelePairing.beta3 F ζ hζ x a = 1)
    (u : Finset (S)) :
    ∃ k ∈ K, ∀ a ∈ u,
      KPGlobalCubicIdelePairing.beta3 F ζ hζ k a.val =
        KPGlobalCubicIdelePairing.beta3 F ζ hζ x a.val := by
  let H := Subgroup.closure (u : Set (S))
  have hpow (a : H) : a ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact KPGlobalCubicIdelePairing.exponent_three F a.val.val
  letI : Finite H := CommGroup.finite_of_fg_isMulTorsion H
    (ExponentExists.isMulTorsion (show Monoid.ExponentExists H from ⟨3, by decide, hpow⟩))
  letI : HasEnoughRootsOfUnity F 3 :=
    ⟨⟨ζ ^ 4, hζ.pow (by decide) (by decide : 12 = 4 * 3)⟩, rootsOfUnity.isCyclic F 3⟩
  letI : HasEnoughRootsOfUnity F (Monoid.exponent H) :=
    HasEnoughRootsOfUnity.of_dvd F (Monoid.exponent_dvd_of_forall_pow_eq_one hpow)
  let r : KPGlobalCubicIdelePairing.D F →* (H →* Fˣ) :=
    MonoidHom.mk' (fun d => (pairingHom F ζ hζ d).comp
      ((S).subtype.comp H.subtype))
      (fun d e => MonoidHom.ext (fun a => by
        change pairingHom F ζ hζ (d * e) a.val.val = _
        exact DFunLike.congr_fun (map_mul (pairingHom F ζ hζ) d e) a.val.val))
  let Φ := K.map r
  let E := CommGroup.subgroupOrderIsoSubgroupMonoidHom H F
  have hr : r x ∈ (E (E.symm (OrderDual.toDual Φ))).ofDual := by
    rw [CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_iff]
    intro a ha
    have hak : ∀ k ∈ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ a.val.val k = 1 := by
      intro k hk
      have hka : KPGlobalCubicIdelePairing.beta3 F ζ hζ k a.val.val = 1 := by
        apply Subtype.ext
        exact (CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff F Φ a).mp ha
          (r k) (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
      have halt := (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).2.2 (k * a.val.val)
      rw [(KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1,
        (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).2.1,
        (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).2.1,
        (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).2.2,
        (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).2.2,
        hka] at halt
      simpa using halt
    exact congrArg Subtype.val (hx a.val.val a.val.property hak)
  rw [E.apply_symm_apply] at hr
  obtain ⟨k, hk, he⟩ := Subgroup.mem_map.mp hr
  refine ⟨k, hk, ?_⟩
  intro a ha
  apply Subtype.ext
  exact DFunLike.congr_fun he ⟨a, Subgroup.subset_closure ha⟩

 def ann (S : Subgroup (KPGlobalCubicIdelePairing.D F)) :
    Subgroup (KPGlobalCubicIdelePairing.D F) where
  carrier := {x | ∀ y ∈ S, pairingHom F ζ hζ x y = 1}
  one_mem' := by intro y hy; simp
  mul_mem' := by intro x z hx hz y hy; simp [map_mul, hx y hy, hz y hy]
  inv_mem' := by intro x hx y hy; simp [map_inv, hx y hy]

private theorem mem_ann (S : Subgroup (KPGlobalCubicIdelePairing.D F))
    (x : KPGlobalCubicIdelePairing.D F) :
    x ∈ ann F ζ hζ S ↔ ∀ y ∈ S, KPGlobalCubicIdelePairing.beta3 F ζ hζ x y = 1 := by
  constructor
  · intro h y hy; apply Subtype.ext; exact h y hy
  · intro h y hy; exact congrArg Subtype.val (h y hy)

private theorem swap_one (x y : KPGlobalCubicIdelePairing.D F)
    (h : KPGlobalCubicIdelePairing.beta3 F ζ hζ x y = 1) :
    KPGlobalCubicIdelePairing.beta3 F ζ hζ y x = 1 := by
  have hb := KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ
  have hh := hb.2.2 (x * y)
  rw [hb.1, hb.2.1, hb.2.1, hb.2.2, hb.2.2, h] at hh
  simpa using hh

private theorem compact_matching
    (S T : Subgroup (KPGlobalCubicIdelePairing.D F))
    (hT : IsCompact (T : Set (KPGlobalCubicIdelePairing.D F)))
    (x : KPGlobalCubicIdelePairing.D F)
    (hx : ∀ a ∈ S, (∀ k ∈ T, KPGlobalCubicIdelePairing.beta3 F ζ hζ a k = 1) →
      KPGlobalCubicIdelePairing.beta3 F ζ hζ x a = 1) :
    ∃ t ∈ T, x * t⁻¹ ∈ ann F ζ hζ S := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  let b := KPGlobalCubicIdelePairing.beta3 F ζ hζ
  let f : S → Set (KPGlobalCubicIdelePairing.D F) := fun a => {k | b k a.val = b x a.val}
  have hclosed : ∀ a, IsClosed (f a) := by
    intro a
    exact isClosed_singleton.preimage
      ((KPGlobalCubicIdelePairing.beta3_continuous F ζ hζ).comp
        (continuous_id.prodMk continuous_const))
  have hfinite : ∀ u : Finset S, ((T : Set _) ∩ ⋂ a ∈ u, f a).Nonempty := by
    intro u
    obtain ⟨k, hk, he⟩ := finite_matching F ζ hζ S T x hx u
    exact ⟨k, hk, Set.mem_iInter.mpr (fun a => Set.mem_iInter.mpr (fun ha => he a ha))⟩
  obtain ⟨k, hk, he⟩ := hT.inter_iInter_nonempty f hclosed hfinite
  refine ⟨k, hk, ?_⟩
  intro a ha
  have hmatch : pairingHom F ζ hζ k a = pairingHom F ζ hζ x a :=
    congrArg Subtype.val (Set.mem_iInter.mp he ⟨a, ha⟩)
  simp only [map_mul, MonoidHom.mul_apply, map_inv, MonoidHom.inv_apply]
  rw [hmatch, mul_inv_cancel]

private theorem maximal_mem_of_annihilates {G : Type*} [CommGroup G]
    (b : G →* (G →* rootsOfUnity 3 F)) (halt : ∀ x, b x x = 1)
    (L : Subgroup G) (hL : KPGlobalProductPolarizationCharacter.IsMaximalIsotropic F (fun x y => b x y) L)
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

private theorem product_ann (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ) :
    ann F ζ hζ (KPGlobalProductPolarizationCharacter.M F ζ hζ P) =
      KPGlobalProductPolarizationCharacter.M F ζ hζ P := by
  ext x
  constructor
  · intro hx
    let b : KPGlobalCubicIdelePairing.D F →* (KPGlobalCubicIdelePairing.D F →* rootsOfUnity 3 F) :=
      MonoidHom.mk' (fun x => MonoidHom.mk' (KPGlobalCubicIdelePairing.beta3 F ζ hζ x)
        (fun y z => (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).2.1 x y z))
        (fun x y => MonoidHom.ext (fun z => (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1 x y z))
    exact maximal_mem_of_annihilates F b
      (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).2.2 _
      (KPGlobalProductPolarizationCharacter.M_maximal_isotropic F ζ hζ P) x
      ((mem_ann F ζ hζ _ x).mp hx)
  · intro hx
    exact (mem_ann F ζ hζ _ x).mpr (fun y hy =>
      (KPGlobalProductPolarizationCharacter.M_maximal_isotropic F ζ hζ P).1 x hx y hy)

private theorem ann_closed (S : Subgroup (KPGlobalCubicIdelePairing.D F)) :
    IsClosed (ann F ζ hζ S : Set (KPGlobalCubicIdelePairing.D F)) := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  have he : (ann F ζ hζ S : Set _) = ⋂ s : S,
      {x | KPGlobalCubicIdelePairing.beta3 F ζ hζ x s.val = 1} := by
    ext x
    change x ∈ ann F ζ hζ S ↔ _
    rw [mem_ann]
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun h s => h s.val s.property, fun h s hs => h ⟨s, hs⟩⟩
  rw [he]
  exact isClosed_iInter (fun s => isClosed_singleton.preimage
    ((KPGlobalCubicIdelePairing.beta3_continuous F ζ hζ).comp
      (continuous_id.prodMk continuous_const)))

private theorem ann_compact
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (K : Subgroup (KPGlobalCubicIdelePairing.D F))
    (hopen : IsOpen (K : Set (KPGlobalCubicIdelePairing.D F))) :
    IsCompact (ann F ζ hζ K : Set (KPGlobalCubicIdelePairing.D F)) := by
  let M := KPGlobalProductPolarizationCharacter.M F ζ hζ P
  let N := ann F ζ hζ K
  let H := M.comap N.subtype
  let KM := K.comap M.subtype
  letI : CompactSpace M := isCompact_iff_compactSpace.mp
    (KPGlobalProductPolarizationCharacter.M_compact_open F ζ hζ P).1
  letI : Finite (M ⧸ KM) :=
    Subgroup.quotient_finite_of_isOpen KM (hopen.preimage continuous_subtype_val)
  let value : N → (M ⧸ KM) → Fˣ := fun x =>
    QuotientGroup.lift KM ((pairingHom F ζ hζ x.val).comp M.subtype)
      (by intro k hk; exact x.property k.val hk)
  let φ : N →* ((M ⧸ KM) → Fˣ) :=
    { toFun := value
      map_one' := by
        funext z
        induction z using QuotientGroup.induction_on with
        | H m => exact DFunLike.congr_fun (map_one (pairingHom F ζ hζ)) m.val
      map_mul' := by
        intro x y
        funext z
        induction z using QuotientGroup.induction_on with
        | H m => exact DFunLike.congr_fun (map_mul (pairingHom F ζ hζ) x.val y.val) m.val }

  let φ3 : N →* ((M ⧸ KM) → rootsOfUnity 3 F) :=
    { toFun x z := ⟨φ x z, by
        induction z using QuotientGroup.induction_on with
        | H m => exact (KPGlobalCubicIdelePairing.beta3 F ζ hζ x.val m.val).property⟩
      map_one' := by funext z; apply Subtype.ext; exact congrFun φ.map_one z
      map_mul' := by intro x y; funext z; apply Subtype.ext; exact congrFun (φ.map_mul x y) z }
  have hker : H ≤ φ3.ker := by
    intro x hx
    funext z
    apply Subtype.ext
    induction z using QuotientGroup.induction_on with
    | H m =>
      exact congrArg Subtype.val
        ((KPGlobalProductPolarizationCharacter.M_maximal_isotropic F ζ hζ P).1 x.val hx m.val m.property)
  let ψ := QuotientGroup.lift H φ3 hker
  have hinj : Function.Injective ψ := by
    apply (injective_iff_map_eq_one ψ).mpr
    intro z
    induction z using QuotientGroup.induction_on with
    | H x =>
      intro hx
      apply (QuotientGroup.eq_one_iff x).mpr
      change x.val ∈ KPGlobalProductPolarizationCharacter.M F ζ hζ P
      rw [← product_ann F ζ hζ P]
      intro m hm
      exact congrArg Subtype.val (congrFun hx (QuotientGroup.mk' KM ⟨m, hm⟩))
  letI : Finite (N ⧸ H) := Finite.of_injective ψ hinj
  choose reps hreps using (QuotientGroup.mk'_surjective H)
  let C : Set (KPGlobalCubicIdelePairing.D F) := (N : Set _) ∩ (M : Set _)
  have hc : IsCompact C := (KPGlobalProductPolarizationCharacter.M_compact_open F ζ hζ P).1.inter_left
    (ann_closed F ζ hζ K)
  have he : (N : Set (KPGlobalCubicIdelePairing.D F)) = ⋃ z : N ⧸ H,
      (fun m : KPGlobalCubicIdelePairing.D F => (reps z).val * m) '' C := by
    ext x
    constructor
    · intro hx
      let n : N := ⟨x, hx⟩
      let z := QuotientGroup.mk' H n
      have hh : QuotientGroup.mk' H (reps z) = QuotientGroup.mk' H n := hreps z
      have hm : (reps z).val⁻¹ * x ∈ M := (QuotientGroup.eq (a := reps z) (b := n)).mp hh
      exact Set.mem_iUnion.mpr ⟨z, (reps z).val⁻¹ * x,
        ⟨N.mul_mem (N.inv_mem (reps z).property) hx, hm⟩, mul_inv_cancel_left _ _⟩
    · intro hx
      obtain ⟨z, m, hm, rfl⟩ := Set.mem_iUnion.mp hx
      exact N.mul_mem (reps z).property hm.1
  rw [he]
  exact isCompact_iUnion (fun z => hc.image (continuous_const.mul continuous_id))

private theorem double_ann
    (K : Subgroup (KPGlobalCubicIdelePairing.D F))
    (hcompact : IsCompact (K : Set (KPGlobalCubicIdelePairing.D F))) :
    ann F ζ hζ (ann F ζ hζ K) = K := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, he⟩ := compact_matching F ζ hζ ⊤ K hcompact x
      (fun a ha hak => (mem_ann F ζ hζ _ x).mp hx a ((mem_ann F ζ hζ _ a).mpr hak))
    have hxk : x * k⁻¹ = 1 := (KPGlobalCubicIdelePairing.beta3_radical_zero F ζ hζ _).mp
      (fun y => (mem_ann F ζ hζ _ _).mp he y (by trivial))
    have heq : x = k := mul_inv_eq_one.mp hxk
    simpa [heq] using hk
  · intro hx
    exact (mem_ann F ζ hζ _ x).mpr (fun y hy =>
      swap_one F ζ hζ y x ((mem_ann F ζ hζ _ y).mp hy x hx))

theorem compact_intersection_annihilator_saturation
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (H : Subgroup (KPGlobalTorusFunctionData.E F ζ hζ))
    (hH : H = KPGlobalCenterRationalCharacter.R F ζ hζ ∨
      H = KPGlobalProductPolarizationCharacter.B F ζ hζ P)
    (K : Subgroup (KPGlobalCubicIdelePairing.D F))
    (hcompact : IsCompact (K : Set (KPGlobalCubicIdelePairing.D F)))
    (hopen : IsOpen (K : Set (KPGlobalCubicIdelePairing.D F)))
    (g : KPGlobalTorusFunctionData.E F ζ hζ) :
    (∀ h : H, KPGlobalProductPolarizationCharacter.pD F ζ hζ h.val ∈ K →
      KPGlobalCubicIdelePairing.beta3 F ζ hζ
        (KPGlobalProductPolarizationCharacter.pD F ζ hζ g)
        (KPGlobalProductPolarizationCharacter.pD F ζ hζ h.val) = 1) ↔
    ∃ (h : H) (x : KPGlobalTorusFunctionData.E F ζ hζ),
      g = h.val * x ∧ ∀ k ∈ K,
        KPGlobalCubicIdelePairing.beta3 F ζ hζ
          (KPGlobalProductPolarizationCharacter.pD F ζ hζ x) k = 1 := by
  let S := if H = KPGlobalCenterRationalCharacter.R F ζ hζ then
      KPGlobalPrincipalCubicLagrangian.A F else KPGlobalProductPolarizationCharacter.M F ζ hζ P
  have hpre : H = S.comap (KPGlobalProductPolarizationCharacter.pD F ζ hζ) := by
    rcases hH with hH | hH
    · simp only [S, if_pos hH]
      exact hH.trans (KPGlobalCenterRationalCharacter.R_eq_principal_preimage F ζ hζ)
    · by_cases hR : H = KPGlobalCenterRationalCharacter.R F ζ hζ
      · rw [hR]
        simp only [S, if_pos hR]
        exact KPGlobalCenterRationalCharacter.R_eq_principal_preimage F ζ hζ
      · simp only [S, if_neg hR]
        exact hH
  have hself : ann F ζ hζ S = S := by
    by_cases hR : H = KPGlobalCenterRationalCharacter.R F ζ hζ
    · simp only [S, if_pos hR]
      ext x
      rw [mem_ann]
      exact Set.ext_iff.mp (KPGlobalPrincipalCubicLagrangian.principal_self_annihilating F ζ hζ) x
    · simpa only [S, if_neg hR] using product_ann F ζ hζ P
  have hsurj : Function.Surjective (KPGlobalProductPolarizationCharacter.pD F ζ hζ) := by
    obtain ⟨T, hT⟩ := KPGlobalProductPolarizationCharacter.exists_finite_compatible_adjustment F ζ hζ P
    have hs := (finite_torus_projection_and_phase_trivial_class_lifts F ζ hζ P T).2.2.1
    intro d
    obtain ⟨x, hx⟩ := hs d
    exact ⟨x.val, hx⟩
  constructor
  · intro hg
    have hgS : ∀ a ∈ S,
        (∀ k ∈ ann F ζ hζ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ a k = 1) →
        KPGlobalCubicIdelePairing.beta3 F ζ hζ
          (KPGlobalProductPolarizationCharacter.pD F ζ hζ g) a = 1 := by
      intro a ha hak
      have haK : a ∈ K := by
        rw [← double_ann F ζ hζ K hcompact]
        exact (mem_ann F ζ hζ _ a).mpr hak
      obtain ⟨h, hh⟩ := hsurj a
      have hmem : h ∈ H := by rw [hpre]; exact show
        KPGlobalProductPolarizationCharacter.pD F ζ hζ h ∈ S from hh.symm ▸ ha
      simpa only [hh] using hg ⟨h, hmem⟩ (hh.symm ▸ haK)
    obtain ⟨k, hk, ha⟩ := compact_matching F ζ hζ S (ann F ζ hζ K)
      (ann_compact F ζ hζ P K hopen) (KPGlobalProductPolarizationCharacter.pD F ζ hζ g) hgS
    rw [hself] at ha
    obtain ⟨h, hh⟩ := hsurj (KPGlobalProductPolarizationCharacter.pD F ζ hζ g * k⁻¹)
    have hmem : h ∈ H := by rw [hpre]; exact show
      KPGlobalProductPolarizationCharacter.pD F ζ hζ h ∈ S from hh.symm ▸ ha
    refine ⟨⟨h, hmem⟩, h⁻¹ * g, by simp, ?_⟩
    have hx : KPGlobalProductPolarizationCharacter.pD F ζ hζ (h⁻¹ * g) = k := by
      rw [map_mul, map_inv, hh]
      simp
    intro y hy
    rw [hx]
    exact (mem_ann F ζ hζ K k).mp hk y hy
  · rintro ⟨h, x, rfl, hx⟩ y hy
    have hhS : KPGlobalProductPolarizationCharacter.pD F ζ hζ h.val ∈ S := by
      have hh := h.property
      exact hpre.le hh
    have hyS : KPGlobalProductPolarizationCharacter.pD F ζ hζ y.val ∈ S := by
      have hh := y.property
      exact hpre.le hh
    have hhorth : KPGlobalCubicIdelePairing.beta3 F ζ hζ
        (KPGlobalProductPolarizationCharacter.pD F ζ hζ h.val)
        (KPGlobalProductPolarizationCharacter.pD F ζ hζ y.val) = 1 := by
      apply (mem_ann F ζ hζ S _).mp
      · rwa [hself]
      · exact hyS
    rw [map_mul, (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1, hhorth, hx _ hy, one_mul]

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

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
 def torusPullbackBridge : KPGlobalTorusFunctionData.E F ζ hζ →* KPGlobalCubicIdelePairing.E F ζ hζ where
  toFun e := ⟨(e.val, KPGlobalTorusFunctionData.p F ζ hζ e),
    (diagonal_formula F ⟨_, e.property⟩).symm⟩
  map_one' := by apply Subtype.ext; exact Prod.ext rfl (map_one _)
  map_mul' x y := by apply Subtype.ext; exact Prod.ext rfl (map_mul _ _ _)

private theorem torusPullbackBridge_injective :
    Function.Injective (torusPullbackBridge F ζ hζ) := by
  intro x y h
  exact Subtype.ext (congrArg (fun t : KPGlobalCubicIdelePairing.E F ζ hζ => t.val.1) h)

private theorem commute_iff_beta (x y : KPGlobalTorusFunctionData.E F ζ hζ) :
    Commute x y ↔ KPGlobalCubicIdelePairing.beta3 F ζ hζ
      (KPGlobalProductPolarizationCharacter.pD F ζ hζ x) (KPGlobalProductPolarizationCharacter.pD F ζ hζ y) = 1 := by
  have h := KPGlobalCubicIdelePairing.commutator_annihilators F ζ hζ
    (torusPullbackBridge F ζ hζ x) (torusPullbackBridge F ζ hζ y)
  constructor
  · intro hc
    exact h.mp (hc.map (torusPullbackBridge F ζ hζ))
  · intro hb
    apply torusPullbackBridge_injective F ζ hζ
    simpa only [map_mul] using (h.mpr hb).eq

private theorem central_difference (x y : KPGlobalTorusFunctionData.E F ζ hζ)
    (h : KPGlobalProductPolarizationCharacter.pD F ζ hζ x =
      KPGlobalProductPolarizationCharacter.pD F ζ hζ y) :
    x * y⁻¹ ∈ KPGlobalTorusFunctionData.Z F ζ hζ := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply ((commute_iff_beta F ζ hζ (x * y⁻¹) g).mpr ?_).symm.eq
  rw [map_mul, map_inv, h, mul_inv_cancel]
  exact (KPGlobalCubicIdelePairing.beta3_radical_zero F ζ hζ 1).mpr rfl _

private theorem commutator_root (x y : KPGlobalTorusFunctionData.E F ζ hζ) :
    x * y * x⁻¹ * y⁻¹ =
      (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ
        (KPGlobalCubicIdelePairing.beta3 F ζ hζ
          (KPGlobalProductPolarizationCharacter.pD F ζ hζ x)
          (KPGlobalProductPolarizationCharacter.pD F ζ hζ y) ^ 4)).val := by
  apply Subtype.ext
  have h := congrArg (fun t : KPGlobalCubicIdelePairing.E F ζ hζ => t.val.1)
    (KPGlobalCubicIdelePairing.actual_torus_commutator F ζ hζ
      (torusPullbackBridge F ζ hζ x) (torusPullbackBridge F ζ hζ y))
  rw [KPGlobalCenterRationalCharacter.centralRoot_formula]
  exact h

 def normalizedB
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P) :
    KPGlobalProductPolarizationCharacter.B F ζ hζ P →* ℂˣ where
  toFun b := KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T b /
    KPGlobalCenterRationalCharacter.positiveComplex (KPGlobalCenterRationalCharacter.nu F ζ hζ b.val)
  map_one' := by simp
  map_mul' a b := by simp [div_mul_div_comm]

theorem right_level_lifts_force_orthogonality_and_phase
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)
    (hT : ∀ (b : KPGlobalProductPolarizationCharacter.B F ζ hζ P)
      (r : KPGlobalCenterRationalCharacter.R F ζ hζ), b.val = r.val →
      KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T b =
        KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ :
      (Q.H = KPGlobalCenterRationalCharacter.R F ζ hζ ∧
        ∀ (r : Q.H) (s : KPGlobalCenterRationalCharacter.R F ζ hζ), r.val = s.val →
          Q.character r = KPGlobalCenterRationalCharacter.lambdaR F ζ hζ s /
            KPGlobalCenterRationalCharacter.positiveComplex
              (KPGlobalCenterRationalCharacter.nu F ζ hζ s.val)) ∨
      (Q.H = KPGlobalProductPolarizationCharacter.B F ζ hζ P ∧
        ∀ (r : Q.H) (s : KPGlobalProductPolarizationCharacter.B F ζ hζ P), r.val = s.val →
          Q.character r = KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T s /
            KPGlobalCenterRationalCharacter.positiveComplex
              (KPGlobalCenterRationalCharacter.nu F ζ hζ s.val)))
    (J : Subgroup (KPGlobalTorusFunctionData.E F ζ hζ))
    (K : Subgroup (KPGlobalCubicIdelePairing.D F))
    (hKM : K ≤ KPGlobalProductPolarizationCharacter.M F ζ hζ P)
    (hlifts : ∀ d ∈ K, ∃ j : KPGlobalProductPolarizationCharacter.B F ζ hζ P,
      j.val ∈ J ∧ KPGlobalProductPolarizationCharacter.pD F ζ hζ j.val = d ∧
      KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T j /
        KPGlobalCenterRationalCharacter.positiveComplex
          (KPGlobalCenterRationalCharacter.nu F ζ hζ j.val) = 1)
    (f : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q)
    (hf : f ∈ KPGlobalTorusFunctionData.RightLevel Q.H Q.character.toMonoidHom J) :
    (∀ g : KPGlobalTorusFunctionData.E F ζ hζ, f.val g ≠ 0 →
      ∀ h : Q.H, KPGlobalProductPolarizationCharacter.pD F ζ hζ h.val ∈ K →
        KPGlobalCubicIdelePairing.beta3 F ζ hζ
          (KPGlobalProductPolarizationCharacter.pD F ζ hζ g)
          (KPGlobalProductPolarizationCharacter.pD F ζ hζ h.val) = 1) ∧
    (∀ k : KPGlobalProductPolarizationCharacter.B F ζ hζ P,
      KPGlobalProductPolarizationCharacter.pD F ζ hζ k.val ∈ K →
      ∀ x : KPGlobalTorusFunctionData.E F ζ hζ,
        (∀ y ∈ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ
          (KPGlobalProductPolarizationCharacter.pD F ζ hζ x) y = 1) →
        f.val (x * k.val) =
          ((KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T k /
            KPGlobalCenterRationalCharacter.positiveComplex
              (KPGlobalCenterRationalCharacter.nu F ζ hζ k.val) : ℂˣ) : ℂ) * f.val x) := by
  let ψ := normalizedB F ζ hζ P T
  have agree (b : KPGlobalProductPolarizationCharacter.B F ζ hζ P)
      (hb : b.val ∈ Q.H) : Q.character ⟨b.val, hb⟩ = ψ b := by
    rcases hQ with ⟨hH, hc⟩ | ⟨hH, hc⟩
    · let r : KPGlobalCenterRationalCharacter.R F ζ hζ := ⟨b.val, hH ▸ hb⟩
      rw [hc ⟨b.val, hb⟩ r rfl]
      change _ = KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T b / _
      rw [hT b r rfl]
    · exact hc ⟨b.val, hb⟩ b rfl
  have right (g j : KPGlobalTorusFunctionData.E F ζ hζ) (hj : j ∈ J) :
      f.val (g * j) = f.val g :=
    KPGlobalTorusFunctionData.rightLevel_covariance Q.H Q.character.toMonoidHom J
      ⟨f, hf⟩ g j hj
  have centralchar (ε : rootsOfUnity 3 F) :
      Q.character ⟨(KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val,
        Q.contains_center (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).property⟩ =
      KPGlobalTorusFunctionData.iota F ζ hζ ε := by
    let z := KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε
    let b : KPGlobalProductPolarizationCharacter.B F ζ hζ P :=
      ⟨z.val, KPGlobalProductPolarizationCharacter.center_le_B F ζ hζ P z.property⟩
    rw [agree b (Q.contains_center z.property)]
    change KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T b /
      KPGlobalCenterRationalCharacter.positiveComplex (KPGlobalCenterRationalCharacter.nu F ζ hζ z.val) = _
    rw [KPGlobalProductPolarizationCharacter.lambdaB_extends_center F ζ hζ P T b z rfl,
      KPGlobalCenterRationalCharacter.nu_centralRoot, map_one, div_one,
      KPGlobalCenterRationalCharacter.omegaA_genuine]
  constructor
  · intro g hg h hh
    obtain ⟨j, hjJ, hjp, hjψ⟩ := hlifts _ hh
    have hz := central_difference F ζ hζ h.val j.val hjp.symm
    have hjH : j.val ∈ Q.H := by
      have hm := Q.H.mul_mem (Q.H.inv_mem (Q.contains_center hz)) h.property
      simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hm
    have hjχ : Q.character ⟨j.val, hjH⟩ = 1 := (agree j hjH).trans hjψ
    let ε := KPGlobalCubicIdelePairing.beta3 F ζ hζ
      (KPGlobalProductPolarizationCharacter.pD F ζ hζ g)
      (KPGlobalProductPolarizationCharacter.pD F ζ hζ j.val) ^ 4
    let z := KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε
    have he : z.val * (j.val * g) = g * j.val := by
      rw [← commutator_root F ζ hζ g j.val]
      group
    have hc : f.val g = (KPGlobalTorusFunctionData.iota F ζ hζ ε : ℂ) * f.val g := by
      calc
        f.val g = f.val (g * j.val) := (right g j.val hjJ).symm
        _ = f.val (z.val * (j.val * g)) := congrArg f.val he.symm
        _ = (Q.character ⟨z.val, Q.contains_center z.property⟩ : ℂ) * f.val (j.val * g) :=
          f.property ⟨z.val, Q.contains_center z.property⟩ (j.val * g)
        _ = (KPGlobalTorusFunctionData.iota F ζ hζ ε : ℂ) * f.val g := by
          rw [centralchar ε, f.property ⟨j.val, hjH⟩ g]
          change _ * ((Q.character ⟨j.val, hjH⟩ : ℂ) * _) = _
          rw [hjχ]
          simp
    have hi : KPGlobalTorusFunctionData.iota F ζ hζ ε = 1 := by
      apply Units.ext
      exact (mul_right_cancel₀ hg (hc.symm.trans (one_mul (f.val g)).symm))
    apply (KPGlobalCubicIdelePairing.coefficient_annihilators F ζ hζ _ _).mp
    rw [← hjp]
    exact hi
  · intro k hk x hx
    obtain ⟨j, hjJ, hjp, hjψ⟩ := hlifts _ hk
    let b := k * j⁻¹
    have hz : b.val ∈ KPGlobalTorusFunctionData.Z F ζ hζ :=
      central_difference F ζ hζ k.val j.val hjp.symm
    have hbH := Q.contains_center hz
    have he : x * k.val = b.val * (x * j.val) := by
      have hc := Subgroup.mem_center_iff.mp hz x
      change x * k.val = (k.val * j.val⁻¹) * (x * j.val)
      calc
        x * k.val = (x * (k.val * j.val⁻¹)) * j.val := by group
        _ = ((k.val * j.val⁻¹) * x) * j.val := by exact congrArg (fun t => t * j.val) hc
        _ = (k.val * j.val⁻¹) * (x * j.val) := by group
    change ψ j = 1 at hjψ
    have hbψ : ψ b = ψ k := by
      change ψ (k * j⁻¹) = ψ k
      rw [map_mul, map_inv, hjψ, inv_one, mul_one]
    calc
      f.val (x * k.val) = f.val (b.val * (x * j.val)) := congrArg f.val he
      _ = (Q.character ⟨b.val, hbH⟩ : ℂ) * f.val (x * j.val) := f.property ⟨b.val, hbH⟩ _
      _ = (ψ k : ℂ) * f.val x := by rw [agree b hbH, hbψ, right x j.val hjJ]

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality

end

section
open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem smooth_level_has_scalar_phase_conditions
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)
    (hT : ∀ (b : KPGlobalProductPolarizationCharacter.B F ζ hζ P)
      (r : KPGlobalCenterRationalCharacter.R F ζ hζ), b.val = r.val →
      KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T b =
        KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ :
      (Q.H = KPGlobalCenterRationalCharacter.R F ζ hζ ∧
        ∀ (r : Q.H) (s : KPGlobalCenterRationalCharacter.R F ζ hζ), r.val = s.val →
          Q.character r = KPGlobalCenterRationalCharacter.lambdaR F ζ hζ s /
            KPGlobalCenterRationalCharacter.positiveComplex
              (KPGlobalCenterRationalCharacter.nu F ζ hζ s.val)) ∨
      (Q.H = KPGlobalProductPolarizationCharacter.B F ζ hζ P ∧
        ∀ (r : Q.H) (s : KPGlobalProductPolarizationCharacter.B F ζ hζ P), r.val = s.val →
          Q.character r = KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T s /
            KPGlobalCenterRationalCharacter.positiveComplex
              (KPGlobalCenterRationalCharacter.nu F ζ hζ s.val)))
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    ∃ K : Subgroup (KPGlobalCubicIdelePairing.D F),
      K ≤ KPGlobalProductPolarizationCharacter.M F ζ hζ P ∧
      IsCompact (K : Set (KPGlobalCubicIdelePairing.D F)) ∧
      IsOpen (K : Set (KPGlobalCubicIdelePairing.D F)) ∧
      K ⊓ KPGlobalPrincipalCubicLagrangian.A F = ⊥ ∧
      ∀ f : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q,
        f ∈ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U →
        (∀ g, (¬ ∃ (h : Q.H) (x : KPGlobalTorusFunctionData.E F ζ hζ),
        g = h.val * x ∧ ∀ k ∈ K,
          KPGlobalCubicIdelePairing.beta3 F ζ hζ
            (KPGlobalProductPolarizationCharacter.pD F ζ hζ x) k = 1) → f.val g = 0) ∧
      (∀ (k : KPGlobalProductPolarizationCharacter.B F ζ hζ P),
        KPGlobalProductPolarizationCharacter.pD F ζ hζ k.val ∈ K →
        ∀ (x : KPGlobalTorusFunctionData.E F ζ hζ),
          (∀ y ∈ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ
            (KPGlobalProductPolarizationCharacter.pD F ζ hζ x) y = 1) →
          f.val (x * k.val) =
            ((KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T k /
              KPGlobalCenterRationalCharacter.positiveComplex
                (KPGlobalCenterRationalCharacter.nu F ζ hζ k.val) : ℂˣ) : ℂ) * f.val x) := by
  obtain ⟨K, hKM, hcompact, hopen, htransverse, hlifts⟩ :=
    (finite_torus_projection_and_phase_trivial_class_lifts F ζ hζ P T).2.2.2 U
  refine ⟨K, hKM, hcompact, hopen, htransverse, ?_⟩
  intro f hf
  have hfRight : f ∈ KPGlobalTorusFunctionData.RightLevel
      Q.H Q.character.toMonoidHom
      ((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) := hf.2
  obtain ⟨horthogonal, hphase⟩ := right_level_lifts_force_orthogonality_and_phase
    F ζ hζ P T hT Q hQ _ K hKM hlifts f hfRight
  refine ⟨?_, hphase⟩
  intro g hg
  by_contra hnonzero
  have hH : Q.H = KPGlobalCenterRationalCharacter.R F ζ hζ ∨
      Q.H = KPGlobalProductPolarizationCharacter.B F ζ hζ P :=
    hQ.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  exact hg ((compact_intersection_annihilator_saturation
    F ζ hζ P Q.H hH K hcompact hopen g).mp (horthogonal g hnonzero))
end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusTensorFibers
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem archSmooth_of_chart_character_one
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hchart : ∀ z : KPGlobalTorusFunctionData.TorusArch F,
      ∃ h : Q.H, h.val = KPGlobalTorusFunctionData.torusArchChart F ζ hζ z ∧
        Q.character h = 1)
    (f : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q) :
    f ∈ KPGlobalTorusFunctionData.ArchSmooth Q.H Q.character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
      (KPGlobalTorusFunctionData.torusArchDomain F) := by
  intro g
  have he : (fun z => f.val (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z * g)) =
      fun _ => f.val g := by
    funext z
    obtain ⟨h, hh, hc⟩ := hchart z
    rw [← hh, f.property h g]
    simp [hc]
  rw [he]
  exact contDiffOn_const

theorem scalar_phase_right_invariance
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (K : Subgroup (KPGlobalCubicIdelePairing.D F))
    (hKM : K ≤ KPGlobalProductPolarizationCharacter.M F ζ hζ P)
    (hiso : ∀ a ∈ K, ∀ b ∈ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ a b = 1)
    (f : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q)
    (hsupport : ∀ g, (¬ ∃ (h : Q.H) (x : KPGlobalTorusFunctionData.E F ζ hζ),
      g = h.val * x ∧ ∀ y ∈ K,
        KPGlobalCubicIdelePairing.beta3 F ζ hζ
          (KPGlobalProductPolarizationCharacter.pD F ζ hζ x) y = 1) → f.val g = 0)
    (hphase : ∀ (b : KPGlobalProductPolarizationCharacter.B F ζ hζ P),
      KPGlobalProductPolarizationCharacter.pD F ζ hζ b.val ∈ K →
      ∀ (x : KPGlobalTorusFunctionData.E F ζ hζ),
        (∀ y ∈ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ
          (KPGlobalProductPolarizationCharacter.pD F ζ hζ x) y = 1) →
        f.val (x * b.val) =
          ((KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T b /
            KPGlobalCenterRationalCharacter.positiveComplex
              (KPGlobalCenterRationalCharacter.nu F ζ hζ b.val) : ℂˣ) : ℂ) * f.val x)
    (j : KPGlobalTorusFunctionData.E F ζ hζ)
    (hj : KPGlobalProductPolarizationCharacter.pD F ζ hζ j ∈ K)
    (hchar : ∀ b : KPGlobalProductPolarizationCharacter.B F ζ hζ P, b.val = j →
      KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T b /
        KPGlobalCenterRationalCharacter.positiveComplex
          (KPGlobalCenterRationalCharacter.nu F ζ hζ b.val) = 1) :
    ∀ g, f.val (g * j) = f.val g := by
  let b : KPGlobalProductPolarizationCharacter.B F ζ hζ P := ⟨j, hKM hj⟩
  have hbj : b.val = j := rfl
  have htranslate (x : KPGlobalTorusFunctionData.E F ζ hζ) :
      (∀ y ∈ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ
        (KPGlobalProductPolarizationCharacter.pD F ζ hζ (x * j)) y = 1) ↔
      (∀ y ∈ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ
        (KPGlobalProductPolarizationCharacter.pD F ζ hζ x) y = 1) := by
    simp only [map_mul, (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1]
    constructor <;> intro hx y hy
    · simpa only [hiso _ hj y hy, mul_one] using hx y hy
    · simpa only [hiso _ hj y hy, mul_one] using hx y hy
  intro g
  by_cases hg : ∃ (h : Q.H) (x : KPGlobalTorusFunctionData.E F ζ hζ),
      g = h.val * x ∧ ∀ y ∈ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ
        (KPGlobalProductPolarizationCharacter.pD F ζ hζ x) y = 1
  · obtain ⟨h, x, rfl, hx⟩ := hg
    rw [mul_assoc, f.property h (x * j), f.property h x]
    have he := hphase b hj x hx
    rw [hchar b hbj] at he
    simpa using congrArg (fun z : ℂ => (Q.character h : ℂ) * z) he
  · rw [hsupport g hg]
    apply hsupport
    rintro ⟨h, x, hxg, hx⟩
    apply hg
    refine ⟨h, x * j⁻¹, ?_, ?_⟩
    · have he := congrArg (fun z => z * j⁻¹) hxg
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using he
    · apply (htranslate (x * j⁻¹)).mp
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hx

theorem scalar_phase_global_covariance
    {G : Type*} [Group G] (H N : Subgroup G) (χ : H →* ℂˣ)
    (f : KPGlobalTorusFunctionData.ScalarFunctions H χ)
    (hsupport : ∀ g, (¬ ∃ (h : H) (x : N), g = h.val * x.val) → f.val g = 0)
    (k : G) (hk : k ∈ N) (c : ℂ)
    (hphase : ∀ x : N, f.val (x.val * k) = c * f.val x.val) :
    ∀ g, f.val (g * k) = c * f.val g := by
  intro g
  by_cases hg : ∃ (h : H) (x : N), g = h.val * x.val
  · obtain ⟨h, x, rfl⟩ := hg
    rw [mul_assoc, f.property h (x.val * k), f.property h x.val, hphase x]
    ring
  · have hgk : ¬ ∃ (h : H) (x : N), g * k = h.val * x.val := by
      rintro ⟨h, x, hx⟩
      apply hg
      refine ⟨h, ⟨x.val * k⁻¹, N.mul_mem x.property (N.inv_mem hk)⟩, ?_⟩
      change g = h.val * (x.val * k⁻¹)
      rw [← mul_assoc, ← hx]
      simp
    rw [hsupport g hg, hsupport (g * k) hgk, mul_zero]

theorem scalar_phase_levels_cofinal
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)
    (hT : ∀ (b : KPGlobalProductPolarizationCharacter.B F ζ hζ P)
      (r : KPGlobalCenterRationalCharacter.R F ζ hζ), b.val = r.val →
      KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T b =
        KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ :
      (Q.H = KPGlobalCenterRationalCharacter.R F ζ hζ ∧
        ∀ (r : Q.H) (s : KPGlobalCenterRationalCharacter.R F ζ hζ), r.val = s.val →
          Q.character r = KPGlobalCenterRationalCharacter.lambdaR F ζ hζ s /
            KPGlobalCenterRationalCharacter.positiveComplex
              (KPGlobalCenterRationalCharacter.nu F ζ hζ s.val)) ∨
      (Q.H = KPGlobalProductPolarizationCharacter.B F ζ hζ P ∧
        ∀ (r : Q.H) (s : KPGlobalProductPolarizationCharacter.B F ζ hζ P), r.val = s.val →
          Q.character r = KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T s /
            KPGlobalCenterRationalCharacter.positiveComplex
              (KPGlobalCenterRationalCharacter.nu F ζ hζ s.val)))
    (S : Subgroup (KPGlobalCubicIdelePairing.D F) →
      Submodule ℂ (KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q))
    (hS : ∀ K f, f ∈ S K ↔
      (∀ g, (¬ ∃ (h : Q.H) (x : KPGlobalTorusFunctionData.E F ζ hζ),
        g = h.val * x ∧ ∀ k ∈ K,
          KPGlobalCubicIdelePairing.beta3 F ζ hζ
            (KPGlobalProductPolarizationCharacter.pD F ζ hζ x) k = 1) → f.val g = 0) ∧
      (∀ (k : KPGlobalProductPolarizationCharacter.B F ζ hζ P),
        KPGlobalProductPolarizationCharacter.pD F ζ hζ k.val ∈ K →
        ∀ (x : KPGlobalTorusFunctionData.E F ζ hζ),
          (∀ y ∈ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ
            (KPGlobalProductPolarizationCharacter.pD F ζ hζ x) y = 1) →
          f.val (x * k.val) =
            ((KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T k /
              KPGlobalCenterRationalCharacter.positiveComplex
                (KPGlobalCenterRationalCharacter.nu F ζ hζ k.val) : ℂˣ) : ℂ) * f.val x)) :
    (∀ K : Subgroup (KPGlobalCubicIdelePairing.D F),
      K ≤ KPGlobalProductPolarizationCharacter.M F ζ hζ P →
      IsCompact (K : Set (KPGlobalCubicIdelePairing.D F)) →
      IsOpen (K : Set (KPGlobalCubicIdelePairing.D F)) →
      K ⊓ KPGlobalPrincipalCubicLagrangian.A F = ⊥ →
      ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
        S K ≤ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U) ∧
    (∀ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∃ K : Subgroup (KPGlobalCubicIdelePairing.D F),
        K ≤ KPGlobalProductPolarizationCharacter.M F ζ hζ P ∧
        IsCompact (K : Set (KPGlobalCubicIdelePairing.D F)) ∧
        IsOpen (K : Set (KPGlobalCubicIdelePairing.D F)) ∧
        K ⊓ KPGlobalPrincipalCubicLagrangian.A F = ⊥ ∧
        KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U ≤ S K) := by
  constructor
  · intro K hKM _hcompact hopen _hdisjoint
    obtain ⟨U, hU⟩ :=
      KPGlobalTorusFiniteStagesCofinality.finite_level_with_trivial_phase
        F ζ hζ P T K hKM hopen
    refine ⟨U, ?_⟩
    intro f hf
    obtain ⟨hsupport, hphase⟩ := (hS K f).mp hf
    constructor
    · exact archSmooth_of_chart_character_one F ζ hζ Q
        (KPGlobalTorusFiniteStagesCofinality.normalized_arch_chart_character_one
          F ζ hζ P T Q hQ) f
    · intro j
      apply Subtype.ext
      funext g
      obtain ⟨hj, hchar⟩ := hU j.val j.property
      exact scalar_phase_right_invariance F ζ hζ P T Q K hKM
        (fun a ha b hb =>
          (KPGlobalProductPolarizationCharacter.M_maximal_isotropic F ζ hζ P).1
            a (hKM ha) b (hKM hb))
        f hsupport hphase j.val hj hchar g
  · intro U
    obtain ⟨K, hKM, hcompact, hopen, hdisjoint, hconditions⟩ :=
      KPGlobalTorusFiniteStagesCofinality.smooth_level_has_scalar_phase_conditions
        F ζ hζ P T hT Q hQ U
    refine ⟨K, hKM, hcompact, hopen, hdisjoint, ?_⟩
    intro f hf
    exact (hS K f).mpr (hconditions f hf)
end
end DedekindZetaZeroFree.KPGlobalTorusTensorFibers

end
