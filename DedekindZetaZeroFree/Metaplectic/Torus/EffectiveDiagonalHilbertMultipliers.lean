module

public import DedekindZetaZeroFree.Metaplectic.Kubota.LocalRootLifts

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPEffectiveDiagonalMultiplier

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def C (v : KPHilbert.Place F) (x y : (KPHilbert.Completion F v)ˣ) : ℂ :=
  (KPLocalCover.genuineCharacter F ζ hζ (KPHilbert.B3 F ζ hζ v x y ^ 2) : ℂ)

theorem C_conjugate (v : KPHilbert.Place F) (x y : (KPHilbert.Completion F v)ˣ) :
    C F ζ hζ v x y =
      star (KPLocalCover.coefficientEmbedding F ζ hζ
        (KPLocalCover.threeToSix F (KPHilbert.B3 F ζ hζ v x y ^ 2)) : ℂ) := by
  rfl

theorem C_eq_B6_square (v : KPHilbert.Place F)
    (x y : (KPHilbert.Completion F v)ˣ) :
    C F ζ hζ v x y =
      (KPLocalCover.coefficientEmbedding F ζ hζ (KPHilbert.B6 F ζ hζ v x y ^ 2) : ℂ) := by
  let r := KPHilbert.B6 F ζ hζ v x y
  have hr : r ^ 6 = 1 := by
    apply Subtype.ext
    exact r.property
  have hi : KPLocalCover.threeToSix F (KPHilbert.B3 F ζ hζ v x y ^ 2) = r ^ 4 := by
    apply Subtype.ext
    change ((r : Fˣ) ^ 2) ^ 2 = (r : Fˣ) ^ 4
    rw [← pow_mul]
  have hp : r ^ 4 = (r ^ 2)⁻¹ := by
    apply (eq_inv_iff_mul_eq_one).2
    rw [← pow_add]
    exact hr
  rw [C_conjugate, hi]
  have hc : (KPLocalCover.coefficientEmbedding F ζ hζ (r ^ 4) : ℂ) ^ 6 = 1 := by
    have h : (r ^ 4) ^ 6 = 1 := by rw [pow_right_comm, hr, one_pow]
    have h' := congrArg (KPLocalCover.coefficientEmbedding F ζ hζ) h
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg Units.val h'
  change (starRingEnd ℂ) (KPLocalCover.coefficientEmbedding F ζ hζ (r ^ 4) : ℂ) = _
  rw [← Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hc (by decide)),
    hp, map_inv, Units.val_inv_eq_inv_val, inv_inv]

private theorem B6_zpow_left (v : KPHilbert.Place F)
    (a b : (KPHilbert.Completion F v)ˣ) (e : ℤ) :
    KPHilbert.B6 F ζ hζ v (a ^ e) b = KPHilbert.B6 F ζ hζ v a b ^ e := by
  let h := MonoidHom.mk' (fun a => KPHilbert.B6 F ζ hζ v a b)
    (fun a c => (KPHilbert.B6_laws F ζ hζ v).1 a c b)
  exact h.map_zpow a e

private theorem B6_zpow_right (v : KPHilbert.Place F)
    (a b : (KPHilbert.Completion F v)ˣ) (e : ℤ) :
    KPHilbert.B6 F ζ hζ v a (b ^ e) = KPHilbert.B6 F ζ hζ v a b ^ e := by
  let h := MonoidHom.mk' (fun b => KPHilbert.B6 F ζ hζ v a b)
    (fun b c => (KPHilbert.B6_laws F ζ hζ v).2.1 a b c)
  exact h.map_zpow b e

section Tame

variable (v : HeightOneSpectrum (𝓞 F))
local instance : ValuativeRel (v.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F v

local instance : IsNonarchimedeanLocalField (v.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v

theorem C_valuation_units
    (hgood : ValuativeRel.valuation (v.adicCompletion F) (6 : v.adicCompletion F) = 1)
    (π : (v.adicCompletion F)ˣ) (hπ : KPHilbert.ordinaryValuation F v π = 1)
    (u t : KPHilbert.LocalIntegerUnits F v) (e f : ℤ) :
    C F ζ hζ (Sum.inr v)
        (π ^ e * KPHilbert.integerUnitInclusion F v u)
        (π ^ f * KPHilbert.integerUnitInclusion F v t) =
      (KPLocalCover.coefficientEmbedding F ζ hζ
        (KPHilbert.residueSixCharacter F v ζ hζ hgood u) : ℂ) ^ (-2 * f) *
      (KPLocalCover.coefficientEmbedding F ζ hζ
        (KPHilbert.residueSixCharacter F v ζ hζ hgood t) : ℂ) ^ (2 * e) := by
  obtain ⟨hl, hr, hs, _, _, hd⟩ := KPHilbert.B6_laws F ζ hζ (Sum.inr v)
  have hu := (KPHilbert.B6_tame F v ζ hζ hgood π hπ u t).1
  have ht := (KPHilbert.B6_tame F v ζ hζ hgood π hπ t u).1
  have hut := (KPHilbert.B6_tame F v ζ hζ hgood π hπ u t).2
  have hup : KPHilbert.B6 F ζ hζ (Sum.inr v)
      (KPHilbert.integerUnitInclusion F v u) π =
      (KPHilbert.residueSixCharacter F v ζ hζ hgood u)⁻¹ := by
    rw [hs, hu]
  rw [C_eq_B6_square, hl, hr, hr, B6_zpow_left, B6_zpow_left,
    B6_zpow_right, B6_zpow_right, (hd π).1, ht, hup, hut]
  simp only [one_zpow, one_mul, mul_one, map_pow, map_mul, map_zpow, map_inv,
    Units.val_pow_eq_pow_val, Units.val_mul, Units.val_zpow_eq_zpow_val,
    Units.val_inv_eq_inv_val]
  simp only [← zpow_natCast, mul_zpow, inv_zpow, ← zpow_mul, ← zpow_neg]
  rw [mul_comm]
  congr 1 <;> congr 1 <;> ring

end Tame

end
end DedekindZetaZeroFree.KPEffectiveDiagonalMultiplier
