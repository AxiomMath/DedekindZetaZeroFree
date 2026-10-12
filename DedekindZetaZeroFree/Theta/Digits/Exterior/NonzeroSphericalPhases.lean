module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.ShiftedResidueCoordinates
public import DedekindZetaZeroFree.Theta.Digits.Exterior.ResiduePhasePowers

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open MomentSources NumberField IsDedekindDomain ThetaExpansion ValuativeRel
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem nonzero_spherical (hR : RootAligned R) (p : ThetaBranch.ExteriorPrime R.A) (x V : Fˣ)
    (hV : ThetaBranch.order p.val V = 0) :
    let g := R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p)
    let H := -V / g
    let z := -(H⁻¹ ^ 2)
    KPSourceConvention.sourceC F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
      (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)
      (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom z) *
      ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p (x * z) =
    sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p) (Characters.psi R p)
      (ThetaBranch.order p.val x + 2) *
      ThetaBranch.symbol R.A R.σ p (ThetaBranch.localUnit R.A R.probe.allowed p x) ^
        (4 + 2 * (ThetaBranch.order p.val x + 2)) *
      ThetaBranch.symbol R.A R.σ p V ^ (4 : ℕ) := by
  dsimp only
  obtain ⟨hH,hz,hxz,huz,huxz⟩ := digit_coordinates R p x V hV
  rw [effective_rational R hR, ThetaBranch.sphericalFactor, hz, hxz, huz, huxz]
  let u := ThetaBranch.localUnit R.A R.probe.allowed p x
  have hu := ThetaBranch.localUnit_order R.A R.probe.allowed p x
  obtain ⟨hr1,hr2⟩ := digit_reductions R p u V hu hV
  unfold ThetaBranch.symbol
  rw [hr1,hr2]
  have hχ : orderOf (ThetaBranch.residueCharacter R.A R.σ p) = 6 := by
    apply DHCubic.orderOf_normalizedSextic_complex F R.A p.val p.property R.σ
    exact (DHCubic.existsUnique_normalizedSextic F R.A p.val p.property).exists.choose_spec
  have hh := digit_powers (ThetaBranch.residueCharacter R.A R.σ p) hχ
    (ThetaBranch.unitResidue p.val u) (ThetaBranch.unitResidue p.val V)
    (ThetaBranch.unitResidue_ne_zero p.val u hu) (ThetaBranch.unitResidue_ne_zero p.val V hV)
    (ThetaBranch.order p.val x + 2)
  have he : -2 * ThetaBranch.order p.val x = -2 * (ThetaBranch.order p.val x + 2 - 2) := by ring
  rw [he]
  rw [show (ThetaBranch.residueCharacter R.A R.σ p (ThetaBranch.unitResidue p.val u) ^ (2 * (2 : ℤ)) *
      ThetaBranch.residueCharacter R.A R.σ p (-(ThetaBranch.unitResidue p.val V)⁻¹ ^ 2) ^
        (-2 * (ThetaBranch.order p.val x + 2 - 2))) *
      (sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p) (Characters.psi R p)
        (ThetaBranch.order p.val x + 2) *
      ThetaBranch.residueCharacter R.A R.σ p
        (-(ThetaBranch.unitResidue p.val u * (ThetaBranch.unitResidue p.val V)⁻¹ ^ 2)) ^
        (2 * (ThetaBranch.order p.val x + 2))) =
      sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p) (Characters.psi R p)
        (ThetaBranch.order p.val x + 2) *
      (ThetaBranch.residueCharacter R.A R.σ p (ThetaBranch.unitResidue p.val u) ^ (4 : ℤ) *
      ThetaBranch.residueCharacter R.A R.σ p (-(ThetaBranch.unitResidue p.val V)⁻¹ ^ 2) ^
        (-2 * (ThetaBranch.order p.val x + 2 - 2)) *
      ThetaBranch.residueCharacter R.A R.σ p
        (-(ThetaBranch.unitResidue p.val u * (ThetaBranch.unitResidue p.val V)⁻¹ ^ 2)) ^
        (2 * (ThetaBranch.order p.val x + 2))) by ring]
  rw [hh]
  ring

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
