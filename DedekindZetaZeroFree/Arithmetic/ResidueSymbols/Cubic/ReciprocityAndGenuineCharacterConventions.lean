module

public import DedekindZetaZeroFree.Metaplectic.Torus.EffectiveDiagonalHilbertMultipliers

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPSourceConvention
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def sourceB6 (v : KPHilbert.Place F) (x y : (KPHilbert.Completion F v)ˣ) :
    rootsOfUnity 6 F :=
  (KPHilbert.B6 F ζ hζ v x y)⁻¹

def ordinaryGenuineCharacter : rootsOfUnity 3 F →* ℂˣ :=
  (KPLocalCover.coefficientEmbedding F ζ hζ).comp (KPLocalCover.threeToSix F)

@[simp] theorem ordinaryGenuineCharacter_apply (z : rootsOfUnity 3 F) :
    ordinaryGenuineCharacter F ζ hζ z =
      KPLocalCover.coefficientEmbedding F ζ hζ (KPLocalCover.threeToSix F z) := rfl

def sourceC (v : KPHilbert.Place F) (x y : (KPHilbert.Completion F v)ˣ) : ℂ :=
  (ordinaryGenuineCharacter F ζ hζ (KPHilbert.B3 F ζ hζ v x y ^ 2) : ℂ)

theorem sourceC_eq_sourceB6_square (v : KPHilbert.Place F)
    (x y : (KPHilbert.Completion F v)ˣ) :
    sourceC F ζ hζ v x y =
      (KPLocalCover.coefficientEmbedding F ζ hζ (sourceB6 F ζ hζ v x y ^ 2) : ℂ) := by
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
  unfold sourceC ordinaryGenuineCharacter
  simp only [MonoidHom.comp_apply, hi, hp, sourceB6, inv_pow]
  rfl

theorem sourceC_eq_actualC_inv (v : KPHilbert.Place F)
    (x y : (KPHilbert.Completion F v)ˣ) :
    sourceC F ζ hζ v x y = (KPEffectiveDiagonalMultiplier.C F ζ hζ v x y)⁻¹ := by
  rw [sourceC_eq_sourceB6_square, KPEffectiveDiagonalMultiplier.C_eq_B6_square]
  simp [sourceB6]

theorem sourceC_eq_actualB6_neg_two (v : KPHilbert.Place F)
    (x y : (KPHilbert.Completion F v)ˣ) :
    sourceC F ζ hζ v x y =
      (KPLocalCover.coefficientEmbedding F ζ hζ (KPHilbert.B6 F ζ hζ v x y) : ℂ) ^
        (-2 : ℤ) := by
  rw [sourceC_eq_sourceB6_square]
  simp [sourceB6, zpow_neg, zpow_ofNat]

section Tame
variable (v : HeightOneSpectrum (𝓞 F))
local instance : ValuativeRel (v.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F v

local instance : IsNonarchimedeanLocalField (v.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v

theorem sourceC_valuation_units
    (hgood : ValuativeRel.valuation (v.adicCompletion F) (6 : v.adicCompletion F) = 1)
    (π : (v.adicCompletion F)ˣ) (hπ : KPHilbert.ordinaryValuation F v π = 1)
    (u t : KPHilbert.LocalIntegerUnits F v) (e f : ℤ) :
    sourceC F ζ hζ (Sum.inr v)
        (π ^ e * KPHilbert.integerUnitInclusion F v u)
        (π ^ f * KPHilbert.integerUnitInclusion F v t) =
      (KPLocalCover.coefficientEmbedding F ζ hζ
        (KPHilbert.residueSixCharacter F v ζ hζ hgood u) : ℂ) ^ (2 * f) *
      (KPLocalCover.coefficientEmbedding F ζ hζ
        (KPHilbert.residueSixCharacter F v ζ hζ hgood t) : ℂ) ^ (-2 * e) := by
  rw [sourceC_eq_actualC_inv,
    KPEffectiveDiagonalMultiplier.C_valuation_units F ζ hζ v hgood π hπ]
  simp [mul_inv, ← zpow_neg, mul_comm]

end Tame

theorem prod_sourceC_arithmetic (A : SArithmeticData F) (x y : A.G) :
    (∏ v : {v // v ∈ A.Sf},
      sourceC F A.zeta12 A.primitive_zeta12 (Sum.inr v.val) (x.2 v) (y.2 v)) =
      (KPLocalCover.coefficientEmbedding F A.zeta12 A.primitive_zeta12 (A.H_S x y) : ℂ) ^
        (-2 : ℤ) := by
  simp only [sourceC_eq_actualB6_neg_two, ← Finset.prod_zpow]
  have hp := KPHilbert.B6_S_product F A x y
  have he := congrArg (KPLocalCover.coefficientEmbedding F A.zeta12 A.primitive_zeta12) hp
  rw [map_prod] at he
  have hc := congrArg Units.val he
  simp only [Units.coe_prod] at hc
  rw [Finset.prod_zpow, hc]

end
end DedekindZetaZeroFree.KPSourceConvention
