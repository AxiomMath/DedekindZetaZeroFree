module

public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources NumberField
open scoped Classical BigOperators
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem character_order (p : ThetaBranch.ExteriorPrime R.A) :
    orderOf (ThetaBranch.residueCharacter R.A R.σ p) = 6 :=
  DHCubic.orderOf_normalizedSextic_complex F R.A p.val p.property R.σ _
    (DHCubic.existsUnique_normalizedSextic F R.A p.val p.property).exists.choose_spec

theorem mask_mul_kernel {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (z : kˣ) (hz : χ z = 1)
    (j : Fin 6) (d : k) :
    sexticFourierMask χ ψ j (z * d) = sexticFourierMask χ ψ j d := by
  have hzero : (z : k) * d = 0 ↔ d = 0 := mul_eq_zero.trans (by simp)
  by_cases hj : j.val = 0
  · simp only [sexticFourierMask, if_pos hj, hzero]
  · have hz' : (χ⁻¹ ^ j.val) (z : k) = 1 := by
      rw [MulChar.pow_apply' χ⁻¹ hj, MulChar.inv_apply_eq_inv', hz]
      simp
    simp only [sexticFourierMask, if_neg hj, hzero, map_mul, hz', one_mul]

theorem mask_mul_sixth {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (hχ : orderOf χ = 6)
    (z : kˣ) (j : Fin 6) (d : k) :
    sexticFourierMask χ ψ j ((z : k) ^ 6 * d) = sexticFourierMask χ ψ j d := by
  have hz : χ ((z ^ 6 : kˣ) : k) = 1 := by
    have h := congrArg (fun c : MulChar k ℂ => c (z : k)) (pow_orderOf_eq_one χ)
    simpa [hχ, MulChar.pow_apply_coe, MulChar.one_apply z.isUnit, map_pow] using h
  exact mask_mul_kernel χ ψ (z ^ 6) hz j d

end DedekindZetaZeroFree.DigitMasks

end
