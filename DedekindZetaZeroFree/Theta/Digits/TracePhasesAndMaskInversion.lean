module

public import DedekindZetaZeroFree.Theta.Digits.RationalMaskFrequencies

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem sextic_fourier_mask_inversion (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) (j : Fin 6) (t : DHCubic.Residue F p.val) :
    (∑ d : DHCubic.Residue F p.val,
      sexticFourierMask (ThetaBranch.residueCharacter R.A R.σ p) (Characters.psi R p) j d *
        Characters.psi R p (t * d)) =
      sexticUnitPower (ThetaBranch.residueCharacter R.A R.σ p) j t := by
  have ho : orderOf (ThetaBranch.residueCharacter R.A R.σ p) = 6 :=
    DHCubic.orderOf_normalizedSextic_complex F R.A p.val p.property R.σ _
      (DHCubic.existsUnique_normalizedSextic F R.A p.val p.property).exists.choose_spec
  have hd := MulChar.orderOf_dvd_card_sub_one (DHCubic.Residue F p.val)
    (ThetaBranch.residueCharacter R.A R.σ p)
  rw [ho] at hd
  obtain ⟨n, hn⟩ := hd
  have hc := Fintype.one_lt_card (α := DHCubic.Residue F p.val)
  have he : Fintype.card (DHCubic.Residue F p.val) = 6 * n + 1 := by omega
  have hq : Nat.Coprime (Fintype.card (DHCubic.Residue F p.val)) 6 := by
    rw [he, Nat.coprime_comm]
    simp
  exact sexticFourierMask_sum _ _ ho (Characters.primitive R p) hq j t

namespace QuotientDescent
abbrev Digits (R : PrincipalMellin.ActualRecipe S η) (m : ThetaReflectionData.Row R.A) :=
  ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)

theorem selected_digit_phase (R : PrincipalMellin.ActualRecipe S η)
    (m : ThetaReflectionData.Row R.A) (a : Fˣ)
    (ha : ∀ p ∈ ThetaDigitAverage.rowPrimes R.A m.val m.property,
      p.valuation F (a : F) ≤ 1) (d : Digits R m) :
    (adelicTraceCharacter F
      (algebraMap F (KPAdeles F) (a : F) * digitParameter R m d) : ℂ) =
    ∏ p : ThetaDigitAverage.rowPrimes R.A m.val m.property,
      let hp := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
      Characters.psi R ⟨p.val, hp⟩ (ThetaBranch.unitResidue p.val a * d p) := by
  exact DedekindZetaZeroFree.DigitMasks.digitParameter_rational_phase R m a ha d

end QuotientDescent
end DedekindZetaZeroFree.ThetaExpansion

end
