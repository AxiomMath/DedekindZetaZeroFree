module

public import DedekindZetaZeroFree.Theta.Digits.SexticReflectedLocalModel

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open scoped Classical

theorem digit_powers {k : Type*} [Field k] (χ : MulChar k ℂ)
    (hχ : orderOf χ = 6) (t v : k) (ht : t ≠ 0) (hv : v ≠ 0) (e : ℤ) :
    χ t ^ (4 : ℤ) * χ (-(v⁻¹ ^ 2)) ^ (-2 * (e - 2)) *
      χ (-(t * v⁻¹ ^ 2)) ^ (2 * e) = χ t ^ (4 + 2 * e) * χ v ^ (4 : ℕ) := by
  have hn : χ (-1 : k) ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, pow_two, ← map_mul]
    simp
  have hi : χ (v⁻¹) = (χ v)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, inv_mul_cancel₀ hv, MulChar.map_one]
  have ht0 : χ t ≠ 0 := MulChar.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr ht)
  have hv0 : χ v ≠ 0 := MulChar.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr hv)
  have h6 : χ v ^ (6 : ℕ) = 1 := by
    have h := congrArg (fun c : MulChar k ℂ => c v) (pow_orderOf_eq_one χ)
    simpa [hχ, MulChar.pow_apply' _ (by norm_num : (6 : ℕ) ≠ 0),
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hv)] using h
  have hn' (n : ℤ) : χ (-1 : k) ^ (2 * n) = 1 := by rw [zpow_mul, hn, one_zpow]
  rw [show -(v⁻¹ ^ 2) = (-1) * v⁻¹ ^ 2 by ring,
    show -(t * v⁻¹ ^ 2) = (-1) * (t * v⁻¹ ^ 2) by ring]
  simp only [map_mul, map_pow, hi, mul_zpow]
  rw [show -2 * (e - 2) = 2 * (-(e - 2)) by ring, hn', hn', one_mul, one_mul]
  simp only [← zpow_natCast, ← zpow_mul, inv_zpow, ← zpow_neg]
  norm_num only [Nat.cast_ofNat] at ⊢
  rw [show χ t ^ (4 : ℤ) * χ v ^ (-2 * (2 * -(e - 2))) *
      (χ t ^ (2 * e) * χ v ^ (-2 * (2 * e))) =
      (χ t ^ (4 : ℤ) * χ t ^ (2 * e)) *
      (χ v ^ (-2 * (2 * -(e - 2))) * χ v ^ (-2 * (2 * e))) by ring]
  rw [← zpow_add₀ hv0, ← zpow_add₀ ht0,
    show -2 * (2 * -(e - 2)) + -2 * (2 * e) = -8 by ring]
  have hv4 : χ v ^ (-8 : ℤ) = χ v ^ (4 : ℕ) := by
    rw [show (-8 : ℤ) = 4 - 12 by norm_num, zpow_sub₀ hv0]
    norm_num only [zpow_ofNat]
    rw [show (12 : ℕ) = 6 * 2 by norm_num, pow_mul, h6, one_pow, div_one]
  rw [hv4]
  rfl

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
