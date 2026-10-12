module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.RationalSphericalWords

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open MomentSources NumberField IsDedekindDomain ThetaExpansion ValuativeRel
open scoped NumberField Classical
open _root_.DedekindZetaZeroFree.ThetaBranch renaming reduction_mul → reduction_mul
open _root_.DedekindZetaZeroFree.ThetaBranch renaming reduction_pow → reduction_pow
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem digit_coordinates (p : ThetaBranch.ExteriorPrime R.A) (x V : Fˣ)
    (hV : ThetaBranch.order p.val V = 0) :
    let g := R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p)
    let H := -V / g
    let z := -(H⁻¹ ^ 2)
    ThetaBranch.order p.val H = -1 ∧ ThetaBranch.order p.val z = 2 ∧
    ThetaBranch.order p.val (x * z) = ThetaBranch.order p.val x + 2 ∧
    ThetaBranch.localUnit R.A R.probe.allowed p z = -(V⁻¹ ^ 2) ∧
    ThetaBranch.localUnit R.A R.probe.allowed p (x * z) =
      -(ThetaBranch.localUnit R.A R.probe.allowed p x * (V⁻¹ ^ 2)) := by
  dsimp only
  let g := R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p)
  have hg : ThetaBranch.order p.val g = 1 := generator_order R p
  have hH : ThetaBranch.order p.val (-V / g) = -1 := by
    simp only [div_eq_mul_inv, order_mul, order_neg, order_inv, hV, hg]
    norm_num
  have hz : ThetaBranch.order p.val (-((-V / g)⁻¹ ^ 2)) = 2 := by
    rw [order_neg, ← zpow_natCast, order_zpow, order_inv, hH]
    norm_num
  have hxz : ThetaBranch.order p.val (x * -((-V / g)⁻¹ ^ 2)) = ThetaBranch.order p.val x + 2 := by
    rw [order_mul, hz]
  refine ⟨hH, hz, hxz, ?_, ?_⟩
  · unfold ThetaBranch.localUnit
    rw [hz]
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, zpow_ofNat]
    field_simp
  · unfold ThetaBranch.localUnit
    rw [hxz]
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]
    rw [zpow_add₀ (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p)).ne_zero]
    norm_num only [zpow_ofNat]
    field_simp

 theorem digit_reductions (p : ThetaBranch.ExteriorPrime R.A) (u V : Fˣ)
    (hu : ThetaBranch.order p.val u = 0) (hV : ThetaBranch.order p.val V = 0) :
    ThetaBranch.unitResidue p.val (-(V⁻¹ ^ 2)) =
      -(ThetaBranch.unitResidue p.val V)⁻¹ ^ 2 ∧
    ThetaBranch.unitResidue p.val (-(u * (V⁻¹ ^ 2))) =
      -(ThetaBranch.unitResidue p.val u * (ThetaBranch.unitResidue p.val V)⁻¹ ^ 2) := by
  have hv : ThetaBranch.order p.val V⁻¹ = 0 := by rw [order_inv, hV, neg_zero]
  have hv2 : ThetaBranch.order p.val (V⁻¹ ^ 2) = 0 := by
    rw [← zpow_natCast, order_zpow, hv, mul_zero]
  constructor
  · rw [reduction_neg _ _ hv2, reduction_pow _ _ hv, reduction_inv _ _ hV]
  · rw [reduction_neg _ _ (by rw [order_mul, hu, hv2, add_zero]),
      reduction_mul _ _ _ hu hv2, reduction_pow _ _ hv, reduction_inv _ _ hV]

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
