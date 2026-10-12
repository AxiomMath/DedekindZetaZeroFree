module

public import DedekindZetaZeroFree.Adeles.Characters.PrincipalCubicLagrangian

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusTensorFibers
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
    (K : Subgroup (KPGlobalCubicIdelePairing.D F))
    (x : KPGlobalCubicIdelePairing.D F)
    (hx : ∀ a ∈ KPGlobalPrincipalCubicLagrangian.A F,
      (∀ k ∈ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ a k = 1) →
      KPGlobalCubicIdelePairing.beta3 F ζ hζ x a = 1)
    (u : Finset (KPGlobalPrincipalCubicLagrangian.A F)) :
    ∃ k ∈ K, ∀ a ∈ u,
      KPGlobalCubicIdelePairing.beta3 F ζ hζ k a.val =
        KPGlobalCubicIdelePairing.beta3 F ζ hζ x a.val := by
  let H := Subgroup.closure (u : Set (KPGlobalPrincipalCubicLagrangian.A F))
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
      ((KPGlobalPrincipalCubicLagrangian.A F).subtype.comp H.subtype))
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

theorem rational_compact_open_annihilator
    (K : Subgroup (KPGlobalCubicIdelePairing.D F))
    (hcompact : IsCompact (K : Set (KPGlobalCubicIdelePairing.D F)))
    (hopen : IsOpen (K : Set (KPGlobalCubicIdelePairing.D F)))
    (hisotropic : ∀ x ∈ K, ∀ y ∈ K,
      KPGlobalCubicIdelePairing.beta3 F ζ hζ x y = 1) :
    ∀ x : KPGlobalCubicIdelePairing.D F,
      (∀ k ∈ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ x k = 1) →
      (∀ a ∈ KPGlobalPrincipalCubicLagrangian.A F,
        (∀ k ∈ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ a k = 1) →
        KPGlobalCubicIdelePairing.beta3 F ζ hζ x a = 1) →
      ∃ a : KPGlobalCubicIdelePairing.D F,
        a ∈ KPGlobalPrincipalCubicLagrangian.A F ∧
        (∀ k ∈ K, KPGlobalCubicIdelePairing.beta3 F ζ hζ a k = 1) ∧
        ∃ k ∈ K, x = a * k := by
  intro x hxK hxA
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  let b := KPGlobalCubicIdelePairing.beta3 F ζ hζ
  let t : KPGlobalPrincipalCubicLagrangian.A F → Set (KPGlobalCubicIdelePairing.D F) :=
    fun a => {k | b k a.val = b x a.val}
  have hclosed : ∀ a, IsClosed (t a) := by
    intro a
    exact isClosed_singleton.preimage
      ((KPGlobalCubicIdelePairing.beta3_continuous F ζ hζ).comp
        (continuous_id.prodMk continuous_const))
  have hfinite : ∀ u : Finset (KPGlobalPrincipalCubicLagrangian.A F),
      ((K : Set _) ∩ ⋂ a ∈ u, t a).Nonempty := by
    intro u
    obtain ⟨k, hk, he⟩ := finite_matching F ζ hζ K x hxA u
    exact ⟨k, hk, Set.mem_iInter.mpr (fun a => Set.mem_iInter.mpr (fun ha => he a ha))⟩
  obtain ⟨k, hk, he⟩ := hcompact.inter_iInter_nonempty t hclosed hfinite
  have hmatch : ∀ a ∈ KPGlobalPrincipalCubicLagrangian.A F, b k a = b x a := by
    intro a ha
    exact Set.mem_iInter.mp he ⟨a, ha⟩
  let a := x * k⁻¹
  have haA : a ∈ KPGlobalPrincipalCubicLagrangian.A F := by
    change a ∈ (KPGlobalPrincipalCubicLagrangian.A F : Set _)
    rw [← KPGlobalPrincipalCubicLagrangian.principal_self_annihilating F ζ hζ]
    intro y hy
    apply Subtype.ext
    change pairingHom F ζ hζ (x * k⁻¹) y = 1
    rw [map_mul, MonoidHom.mul_apply, map_inv, MonoidHom.inv_apply]
    have h : pairingHom F ζ hζ k y = pairingHom F ζ hζ x y :=
      congrArg Subtype.val (hmatch y hy)
    rw [h, mul_inv_cancel]
  refine ⟨a, haA, ?_, k, hk, ?_⟩
  · intro y hy
    apply Subtype.ext
    change pairingHom F ζ hζ (x * k⁻¹) y = 1
    rw [map_mul, MonoidHom.mul_apply, map_inv, MonoidHom.inv_apply]
    have hxy : pairingHom F ζ hζ x y = 1 := congrArg Subtype.val (hxK y hy)
    have hky : pairingHom F ζ hζ k y = 1 := congrArg Subtype.val (hisotropic k hk y hy)
    rw [hxy, hky, inv_one, mul_one]
  · simp [a]
end
end DedekindZetaZeroFree.KPGlobalTorusTensorFibers
