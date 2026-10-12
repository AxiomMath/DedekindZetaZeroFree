module

public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section

open scoped BigOperators

namespace DedekindZetaZeroFree.Hecke.Theta

variable {H : Type*} [CommGroup H]

def weightedInverseClassEquiv (d : H) : H ≃ H where
  toFun c := d⁻¹ * c⁻¹
  invFun c := d⁻¹ * c⁻¹
  left_inv := by
    intro c
    simp [mul_inv_rev, mul_comm, mul_left_comm]
  right_inv := by
    intro c
    simp [mul_inv_rev, mul_comm, mul_left_comm]

@[simp] theorem weightedInverseClassEquiv_apply (d c : H) :
    weightedInverseClassEquiv d c = d⁻¹ * c⁻¹ := rfl

theorem weightedInverseClassEquiv_involutive (d : H) :
    Function.Involutive (weightedInverseClassEquiv d) := by
  intro c
  simp [mul_inv_rev, mul_comm, mul_left_comm]

theorem weightedInvolution_sum [Fintype H] (ψ : H →* ℂ)
    (hψ : ∀ c : H, ‖ψ c‖ = 1) (d : H) (B : H → ℂ) :
    (∑ c : H, ψ c * B (weightedInverseClassEquiv d c)) =
      ψ (d⁻¹) * ∑ c : H, (starRingEnd ℂ) (ψ c) * B c := by
  calc
    (∑ c : H, ψ c * B (weightedInverseClassEquiv d c)) =
        ∑ c : H, ψ (weightedInverseClassEquiv d c) * B c := by
      symm
      simpa only [(weightedInverseClassEquiv_involutive d) _] using
        (weightedInverseClassEquiv d).sum_comp
          (fun c => ψ c * B (weightedInverseClassEquiv d c))
    _ = ψ (d⁻¹) * ∑ c : H, (starRingEnd ℂ) (ψ c) * B c := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      simp only [weightedInverseClassEquiv_apply, map_mul, map_inv,
        Complex.inv_eq_conj (hψ c), mul_assoc]

theorem weightedInvolution_factor_ne_zero (ψ : H →* ℂ)
    (hψ : ∀ c : H, ‖ψ c‖ = 1) (d : H) : ψ (d⁻¹) ≠ 0 := by
  intro h
  have hnorm := hψ (d⁻¹)
  rw [h, norm_zero] at hnorm
  exact zero_ne_one hnorm

end DedekindZetaZeroFree.Hecke.Theta

end
