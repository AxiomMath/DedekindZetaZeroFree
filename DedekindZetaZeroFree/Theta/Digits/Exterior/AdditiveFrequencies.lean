module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.NonzeroSphericalPhases

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open MomentSources NumberField IsDedekindDomain ThetaExpansion ValuativeRel
open scoped NumberField Classical
open _root_.DedekindZetaZeroFree.ThetaBranch renaming reduction_mul → reduction_mul
open _root_.DedekindZetaZeroFree.ThetaBranch renaming reduction_one → reduction_one
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem additive_digit (p : ThetaBranch.ExteriorPrime R.A) (x V : Fˣ)
    (hV : ThetaBranch.order p.val V = 0) (he : 0 ≤ ThetaBranch.order p.val x + 2) :
    (ResidueTrace.localTraceCharacter p.val
      (algebraMap F (p.val.adicCompletion F)
        (x.val * ((-V / R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : Fˣ).val)⁻¹)) : ℂ) =
      if ThetaBranch.order p.val x + 2 = 0 then
        Characters.psi R p
          (ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed p x) /
            ThetaBranch.unitResidue p.val V) else 1 := by
  let g := R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p)
  let a := x * g ^ (2 : ℕ) / V
  have ha : ThetaBranch.order p.val a = ThetaBranch.order p.val x + 2 := by
    simp only [a, div_eq_mul_inv, order_mul, ← zpow_natCast, order_zpow, order_inv,
      hV]
    rw [show ThetaBranch.order p.val g = 1 from generator_order R p]
    ring
  have hi : p.val.valuation F a.val ≤ 1 := by
    have hh := integral_of_order_nonneg p.val a (ha ▸ he)
    letI : (Valued.v : Valuation (p.val.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    have hv := ((ValuativeRel.isEquiv (valuation (p.val.adicCompletion F))
      (Valued.v : Valuation (p.val.adicCompletion F) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one).mp hh
    change Valued.v ((a.val : F) : p.val.adicCompletion F) ≤ 1 at hv
    rwa [HeightOneSpectrum.adicCompletion.valued_coe] at hv
  have hp := DigitMasks.rational_local_phase R p a hi (1 : 𝓞 F)
  simp only [map_one, mul_neg_one, mul_one] at hp
  have harg : algebraMap F (p.val.adicCompletion F)
      (x.val * ((-V / g : Fˣ).val)⁻¹) =
      -(algebraMap F (p.val.adicCompletion F) a.val) /
        algebraMap F (p.val.adicCompletion F) g.val := by
    simp only [a, Units.val_mul, Units.val_div_eq_div_val, Units.val_neg, Units.val_pow_eq_pow_val,
      map_neg, map_div₀, map_mul, map_pow]
    simp only [map_inv₀, map_div₀, map_neg]
    field_simp
  rw [harg, hp]
  by_cases h0 : ThetaBranch.order p.val x + 2 = 0
  · rw [if_pos h0]
    have hx : ThetaBranch.order p.val x = -2 := by omega
    have hau : a = ThetaBranch.localUnit R.A R.probe.allowed p x * V⁻¹ := by
      unfold ThetaBranch.localUnit
      rw [hx]
      simp only [a, div_eq_mul_inv, zpow_neg, zpow_ofNat, inv_inv]
      rfl
    rw [hau, reduction_mul _ _ _ (ThetaBranch.localUnit_order R.A R.probe.allowed p x)
      (by rw [order_inv,hV,neg_zero]), reduction_inv _ _ hV, div_eq_mul_inv]
  · rw [if_neg h0]
    have hano : ThetaBranch.order p.val a ≠ 0 := by rwa [ha]
    simp [ThetaBranch.unitResidue, hano]

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
