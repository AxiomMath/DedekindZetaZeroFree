module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.IdeleUnitValuationPairing
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.TameCubicHilbertDetection
public import DedekindZetaZeroFree.Metaplectic.Torus.TameValuationCoordinates

@[expose] public section

section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.RepresentationTheory.KPGlobalCubicIdelePairingRaw
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
 def charUnitsEquiv (G K : Type*) [CommGroup G] [Field K]
    (hp : ∀ x : G, x ^ 3 = 1) : (G →* rootsOfUnity 3 K) ≃ (G →* Kˣ) where
  toFun f := (rootsOfUnity 3 K).subtype.comp f
  invFun f := f.codRestrict _ (by intro x; change f x ^ 3 = 1; rw [← map_pow, hp, map_one])
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
private theorem charCard (G K : Type*) [CommGroup G] [Finite G] [Field K]
    (z : K) (hz : IsPrimitiveRoot z 3) (hp : ∀ x : G, x ^ 3 = 1) :
    Nat.card (G →* rootsOfUnity 3 K) = Nat.card G := by
  letI : HasEnoughRootsOfUnity K 3 := ⟨⟨z, hz⟩, inferInstance⟩
  letI : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd K (Monoid.exponent_dvd_of_forall_pow_eq_one hp)
  rw [Nat.card_congr (charUnitsEquiv G K hp)]
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G K
private theorem charSeparate (G K : Type*) [CommGroup G] [Finite G] [Field K]
    (z : K) (hz : IsPrimitiveRoot z 3) (hp : ∀ x : G, x ^ 3 = 1)
    (x y : G) (h : ∀ χ : G →* rootsOfUnity 3 K, χ x = χ y) : x = y := by
  letI : HasEnoughRootsOfUnity K 3 := ⟨⟨z, hz⟩, inferInstance⟩
  letI : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd K (Monoid.exponent_dvd_of_forall_pow_eq_one hp)
  apply (CommGroup.forall_apply_eq_apply_iff G (M := K)).mp
  intro χ
  exact congrArg Subtype.val (h ((charUnitsEquiv G K hp).symm χ))
private theorem isotropicDuality (G K : Type*) [CommGroup G] [Finite G] [Field K]
    (z : K) (hz : IsPrimitiveRoot z 3) (hp : ∀ x : G, x ^ 3 = 1)
    (B : G →* G →* rootsOfUnity 3 K)
    (hnd : ∀ x, (∀ y, B x y = 1) → x = 1)
    (H : Subgroup G) (hi : ∀ x y : H, B x.val y.val = 1)
    (hc : Nat.card H = Nat.card (G ⧸ H)) :
    (∀ χ : (G ⧸ H) →* rootsOfUnity 3 K,
      ∃! x : H, ∀ y, QuotientGroup.lift H (B x.val) (by
        intro a ha; exact hi x ⟨a, ha⟩) y = χ y) ∧
    (∀ χ : H →* rootsOfUnity 3 K,
      ∃! y : G ⧸ H, ∀ x : H, QuotientGroup.lift H (B x.val) (by
        intro a ha; exact hi x ⟨a, ha⟩) y = χ x) := by
  let L : H →* ((G ⧸ H) →* rootsOfUnity 3 K) := {
    toFun x := QuotientGroup.lift H (B x.val) (by intro a ha; exact hi x ⟨a, ha⟩)
    map_one' := by apply MonoidHom.ext; intro a; induction a using QuotientGroup.induction_on; simp
    map_mul' := by
      intro x y; apply MonoidHom.ext; intro a
      induction a using QuotientGroup.induction_on with
      | H a => change B (x.val * y.val) a = B x.val a * B y.val a; simp }
  have hq : ∀ x : G ⧸ H, x ^ 3 = 1 := by
    intro x; induction x using QuotientGroup.induction_on with
    | H x => change (QuotientGroup.mk' H x) ^ 3 = 1; rw [← map_pow, hp, map_one]
  have hu : ∀ x : H, x ^ 3 = 1 := by intro x; apply Subtype.ext; exact hp x.val
  have hinj : Function.Injective L := by
    intro x y he
    have he' : ∀ a : G, B x.val a = B y.val a := by
      intro a; exact DFunLike.congr_fun he (QuotientGroup.mk' H a)
    apply Subtype.ext
    apply mul_inv_eq_one.mp
    apply hnd
    intro a
    simp [he', map_mul, map_inv]
  have hfin : Finite ((G ⧸ H) →* rootsOfUnity 3 K) :=
    Nat.finite_of_card_ne_zero (by rw [charCard _ K z hz hq]; exact Nat.card_pos.ne')
  letI := hfin
  have hL : Function.Bijective L :=
    (Nat.bijective_iff_injective_and_card L).mpr ⟨hinj, by rw [charCard _ K z hz hq]; exact hc⟩
  let R : (G ⧸ H) → (H →* rootsOfUnity 3 K) := fun a => {
    toFun x := L x a
    map_one' := by simp
    map_mul' := by intro x y; simp }
  have hRinj : Function.Injective R := by
    intro a b hab
    apply charSeparate _ K z hz hq a b
    intro χ
    obtain ⟨x, rfl⟩ := hL.2 χ
    exact DFunLike.congr_fun hab x
  have hfinU : Finite (H →* rootsOfUnity 3 K) :=
    Nat.finite_of_card_ne_zero (by rw [charCard _ K z hz hu]; exact Nat.card_pos.ne')
  letI := hfinU
  have hR : Function.Bijective R :=
    (Nat.bijective_iff_injective_and_card R).mpr ⟨hRinj, by rw [charCard _ K z hz hu]; exact hc.symm⟩
  constructor
  · intro χ
    obtain ⟨x, hx⟩ := hL.2 χ
    refine ⟨x, fun a => DFunLike.congr_fun hx a, ?_⟩
    intro y hy
    exact hL.1 (by apply MonoidHom.ext; intro a; exact (hy a).trans (DFunLike.congr_fun hx a).symm)
  · intro χ
    obtain ⟨a, ha⟩ := hR.2 χ
    refine ⟨a, fun x => DFunLike.congr_fun ha x, ?_⟩
    intro b hb
    exact hR.1 (by apply MonoidHom.ext; intro x; exact (hb x).trans (DFunLike.congr_fun ha x).symm)
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
include ζ hζ in
private theorem localData (q : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ KPAdelicCoverRestrictedProduct.Bad F q) :
    Finite (LocalD F (Sum.inr q)) ∧ Nat.card (U F (Sum.inr q)) = 3 ∧
      Nat.card (LocalD F (Sum.inr q)) = 9 := by
  let K := q.adicCompletion F
  letI : ValuativeRel K := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
  letI : IsNonarchimedeanLocalField K := ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
  let z : K := algebraMap F K (ζ ^ 4)
  have hz : IsPrimitiveRoot z 3 := (KPHilbert.primitive_three F ζ hζ).map_of_injective (algebraMap F K).injective
  have htame : (3 : (ValuativeRel.valuation K).integer) ∉ IsLocalRing.maximalIdeal _ := by
    change (3 : KPTameCompact.O F q) ∉ KPTameCompact.p F q
    have hv : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3 := fun h => hgood (Or.inr h)
    letI : Nontrivial (KPTameCompact.O F q ⧸ KPTameCompact.p F q) :=
      Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal (KPTameCompact.O F q)).ne_top
    letI : (KPTameCompact.p F q).IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
    let f := Ideal.Quotient.mk (KPTameCompact.p F q)
    letI : IsLocalHom f := IsLocalHom.of_surjective f Ideal.Quotient.mk_surjective
    have hu : IsUnit (3 : KPTameCompact.O F q) := by
      apply isUnit_of_map_unit f
      letI : Field (KPTameCompact.O F q ⧸ KPTameCompact.p F q) := Ideal.Quotient.field _
      apply isUnit_iff_ne_zero.mpr
      simpa only [f, map_ofNat, Nat.cast_ofNat] using
        CharP.cast_ne_zero_of_ne_of_prime (KPTameCompact.O F q ⧸ KPTameCompact.p F q) Nat.prime_three hv
    exact fun h => (IsLocalRing.mem_maximalIdeal _).mp h (by simpa only [mem_nonunits_iff] using hu)
  have h9 : Nat.card (LocalD F (Sum.inr q)) = 9 := KPLocalTorus.card_cubeClasses_tame K z hz htame
  have hf : Finite (LocalD F (Sum.inr q)) := KPLocalTorus.finite_cubeClasses K z hz
  have hidx : (KPCubicUnitIndices.cubeUnits K).index = 3 := by
    have hh := KPCubicHaarTransport.field_cube_index K
    change Nat.card (LocalD F (Sum.inr q)) = 3 * (KPCubicUnitIndices.cubeUnits K).index at hh
    rw [h9] at hh
    omega
  let f : KPHilbert.LocalIntegerUnits F q →* LocalD F (Sum.inr q) :=
    (localClass F (Sum.inr q)).comp (KPHilbert.integerUnitInclusion F q)
  have hr : f.range = U F (Sum.inr q) := by
    exact MonoidHom.range_comp _ _
  have hk : f.ker = KPCubicUnitIndices.cubeUnits K := by
    ext u
    change localClass F (Sum.inr q) (KPHilbert.integerUnitInclusion F q u) = 1 ↔ _
    rw [show localClass F (Sum.inr q) = QuotientGroup.mk' (CubicCharacters.cubes Kˣ) from rfl]
    change ((KPHilbert.integerUnitInclusion F q u : Kˣ) : Kˣ ⧸ CubicCharacters.cubes Kˣ) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact (LocalFieldTheory.IsNonarchimedeanLocalField.mem_powMonoidHom_range_integerUnits_iff K 3 u).symm
  have h3 : Nat.card (U F (Sum.inr q)) = 3 := by
    rw [← hr, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hk]
    exact hidx
  exact ⟨hf, h3, h9⟩

theorem tame_arithmetic_unit_valuation_duality (q : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ KPAdelicCoverRestrictedProduct.Bad F q) :
    (∀ χ : LocalValuationClasses F (Sum.inr q) →* rootsOfUnity 3 F,
      ∃! u : U F (Sum.inr q), ∀ a,
        unitValuationPairing F ζ hζ q hgood u a = χ a) ∧
    (∀ χ : U F (Sum.inr q) →* rootsOfUnity 3 F,
      ∃! a : LocalValuationClasses F (Sum.inr q), ∀ u,
        unitValuationPairing F ζ hζ q hgood u a = χ u) := by
  obtain ⟨hf, h3, h9⟩ := localData F ζ hζ q hgood
  letI := hf
  let B : LocalD F (Sum.inr q) →* LocalD F (Sum.inr q) →* rootsOfUnity 3 F :=
    KPHilbert.finiteThreePairing F ζ hζ q
  have heq : ∀ a b, localPairing F ζ hζ (Sum.inr q) a b = B a b := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b => exact KPHilbert.B3_canonical F ζ hζ q a b
  have hp : ∀ a : LocalD F (Sum.inr q), a ^ 3 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H a =>
      change (localClass F (Sum.inr q) a) ^ 3 = 1
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
  have hnd : ∀ a, (∀ b, B a b = 1) → a = 1 := by
    exact NormalizedSymbolTransport.inverseTransport_left_nondegenerate
      (KPHilbert.finiteRootsThree F ζ hζ q) _
      (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F 3
        (KPHilbert.rootsThree F ζ hζ) q).2.2.1.1
  have hi : ∀ a b : U F (Sum.inr q), B a.val b.val = 1 := by
    intro a b
    rw [← heq]
    exact tame_unit_isotropic F ζ hζ q hgood _ _ a.property b.property
  have hc : Nat.card (U F (Sum.inr q)) = Nat.card (LocalValuationClasses F (Sum.inr q)) := by
    have hh := (U F (Sum.inr q)).card_eq_card_quotient_mul_card_subgroup
    change Nat.card (LocalD F (Sum.inr q)) =
      Nat.card (LocalValuationClasses F (Sum.inr q)) * Nat.card (U F (Sum.inr q)) at hh
    rw [h3, h9] at hh
    rw [h3]
    omega
  have hh := isotropicDuality _ F (ζ ^ 4) (KPHilbert.primitive_three F ζ hζ) hp B hnd
    (U F (Sum.inr q)) hi hc
  have heq' (u : U F (Sum.inr q)) (a : LocalValuationClasses F (Sum.inr q)) :
      unitValuationPairing F ζ hζ q hgood u a =
      QuotientGroup.lift (U F (Sum.inr q)) (B u.val) (by
        intro x hx; exact hi u ⟨x, hx⟩) a := by
    induction a using QuotientGroup.induction_on with
    | H a => exact heq u.val a
  simpa only [heq'] using hh
end
end DedekindZetaZeroFree.RepresentationTheory.KPGlobalCubicIdelePairingRaw

end
