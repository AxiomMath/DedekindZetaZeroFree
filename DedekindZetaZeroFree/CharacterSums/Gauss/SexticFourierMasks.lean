module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped BigOperators
open Classical

def sexticMaskGaussSum {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (j : Fin 6) : ℂ :=
  gaussSum (χ⁻¹ ^ j.val) ψ

def sexticFourierMask {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (j : Fin 6) (v : k) : ℂ :=
  if j.val = 0 then
    if v = 0 then 1 - (Fintype.card k : ℂ)⁻¹ else -(Fintype.card k : ℂ)⁻¹
  else if v = 0 then 0
  else (χ⁻¹ ^ j.val) v / sexticMaskGaussSum χ ψ j

def sexticUnitPower {k : Type*} [Field k] (χ : MulChar k ℂ)
    (j : Fin 6) (t : k) : ℂ :=
  if IsUnit t then χ t ^ j.val else 0

private theorem mask_power_ne_one {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (hχ : orderOf χ = 6) (j : Fin 6) (hj : j.val ≠ 0) :
    χ⁻¹ ^ j.val ≠ 1 := by
  apply pow_ne_one_of_lt_orderOf hj
  simpa [orderOf_inv, hχ] using j.isLt

theorem sexticMaskGaussSum_norm {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (hχ : orderOf χ = 6) (hψ : ψ.IsPrimitive)
    (hQ : Nat.Coprime (Fintype.card k) 6)
    (j : Fin 6) (hj : j.val ≠ 0) :
    ‖sexticMaskGaussSum χ ψ j‖ = Real.sqrt (Fintype.card k : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card (mask_power_ne_one χ hχ j hj) hψ
  rw [← star_gaussSum_eq, Complex.star_def, Complex.mul_conj'] at h
  have hs : ‖sexticMaskGaussSum χ ψ j‖ ^ 2 = (Fintype.card k : ℝ) := by
    exact_mod_cast h
  exact ((Real.sqrt_eq_iff_eq_sq (by positivity) (norm_nonneg _)).mpr hs.symm).symm

theorem sexticMaskGaussSum_ne_zero {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (hχ : orderOf χ = 6) (hψ : ψ.IsPrimitive)
    (hQ : Nat.Coprime (Fintype.card k) 6)
    (j : Fin 6) (hj : j.val ≠ 0) :
    sexticMaskGaussSum χ ψ j ≠ 0 := by
  exact gaussSum_ne_zero_of_nontrivial (by exact_mod_cast Fintype.card_ne_zero)
    (mask_power_ne_one χ hχ j hj) hψ

theorem sexticFourierMask_sum {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (hχ : orderOf χ = 6) (hψ : ψ.IsPrimitive)
    (hQ : Nat.Coprime (Fintype.card k) 6)
    (j : Fin 6) (t : k) :
    (∑ v : k, sexticFourierMask χ ψ j v * ψ (t * v)) =
      sexticUnitPower χ j t := by
  by_cases hj : j.val = 0
  · have hm (v : k) : sexticFourierMask χ ψ j v =
        (if v = 0 then 1 else 0) - (Fintype.card k : ℂ)⁻¹ := by
      by_cases hv : v = 0 <;> simp [sexticFourierMask, hj, hv]
    simp_rw [hm, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hs : (∑ v : k, ψ (t * v)) =
        if t = 0 then (Fintype.card k : ℂ) else 0 := by
      simpa [mul_comm] using AddChar.sum_mulShift t hψ
    rw [hs]
    by_cases ht : t = 0
    · simp [ht, sexticUnitPower, hj, Fintype.card_ne_zero]
    · simp [ht, sexticUnitPower, hj, isUnit_iff_ne_zero]
  · have hm (v : k) : sexticFourierMask χ ψ j v =
        (χ⁻¹ ^ j.val) v / sexticMaskGaussSum χ ψ j := by
      by_cases hv : v = 0
      · subst v
        simp only [sexticFourierMask, if_neg hj, if_pos rfl, MulChar.map_zero, zero_div, ite_true]
      · simp only [sexticFourierMask, if_neg hj, if_neg hv]
    simp_rw [hm, div_mul_eq_mul_div, ← Finset.sum_div]
    by_cases ht : t = 0
    · subst t
      simp only [zero_mul, AddChar.map_zero_eq_one, mul_one]
      rw [MulChar.sum_eq_zero_of_ne_one (mask_power_ne_one χ hχ j hj)]
      simp [sexticUnitPower]
    · let u := (isUnit_iff_ne_zero.mpr ht).unit
      have hs : (∑ v : k, (χ⁻¹ ^ j.val) v * ψ (t * v)) =
          (χ ^ j.val) t * sexticMaskGaussSum χ ψ j := by
        have h := gaussSum_mulShift_eq (χ⁻¹ ^ j.val) ψ u
        simpa [gaussSum, AddChar.mulShift_apply, u, inv_pow, sexticMaskGaussSum] using h
      rw [hs, mul_div_cancel_right₀ _ (sexticMaskGaussSum_ne_zero χ ψ hχ hψ hQ j hj)]
      simp [sexticUnitPower, isUnit_iff_ne_zero, ht, MulChar.pow_apply' χ hj]

end
end DedekindZetaZeroFree
