module

public import DedekindZetaZeroFree.CharacterSums.Gauss.SexticFourierMasks

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped BigOperators
open Classical

def sexticSphericalCoefficient {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (e : ℤ) : ℂ :=
  if e < 0 then 0 else
    if e % 3 = 0 then (Fintype.card k : ℂ) ^ (-(e / 3))
    else if e % 3 = 1 then
      (Fintype.card k : ℂ) ^ (-(e / 3)) *
        (Real.sqrt (Fintype.card k : ℝ) : ℂ)⁻¹ *
        ((Real.sqrt (Fintype.card k : ℝ) : ℂ)⁻¹ * gaussSum (χ ^ 2) ψ)
    else 0

def sexticReflectedNonzeroDigits {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (j : Fin 6) (e : ℤ) (t : k) : ℂ :=
  sexticSphericalCoefficient χ ψ e * (χ t) ^ (4 + 2 * e) *
    ∑ v ∈ (Finset.univ.erase (0 : k)),
      sexticFourierMask χ ψ j v * χ v ^ 4 *
        (if e = 0 then ψ (t / v) else 1)

def sexticReflectedDepthZeroScalar {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (j : Fin 6) : ℂ :=
  if j.val = 0 then
    -(Fintype.card k : ℂ)⁻¹ * gaussSum (χ ^ 2) ψ
  else gaussSum (χ ^ ((j.val + 2) % 6)) ψ / sexticMaskGaussSum χ ψ j

def sexticReflectedDigitModel {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (j : Fin 6) (e : ℤ) (t : k) : ℂ :=
  sexticReflectedNonzeroDigits χ ψ j e t +
    sexticFourierMask χ ψ j 0 *
      (sexticSphericalCoefficient χ ψ (e - 2) * (χ t) ^ (2 * (e - 2)))

private lemma reflected_pow_six {k : Type*} [Field k] (χ : MulChar k ℂ)
    (hχ : orderOf χ = 6) (v : k) (hv : v ≠ 0) : χ v ^ 6 = 1 := by
  have h := congrArg (fun c : MulChar k ℂ => c v) (pow_orderOf_eq_one χ)
  simpa [hχ, MulChar.pow_apply' χ (by norm_num : (6 : ℕ) ≠ 0),
    MulChar.one_apply (isUnit_iff_ne_zero.mpr hv)] using h

private lemma reflected_pow_ne_one {k : Type*} [Field k] (χ : MulChar k ℂ)
    (hχ : orderOf χ = 6) (n : ℕ) (hn : ¬6 ∣ n) : χ ^ n ≠ 1 := by
  intro hp
  have hd := orderOf_dvd_iff_pow_eq_one.mpr hp
  exact hn (by simpa [hχ] using hd)

private lemma reflected_twist {k : Type*} [Field k] (χ : MulChar k ℂ)
    (hχ : orderOf χ = 6) (j : Fin 6) (v : k) (hv : v ≠ 0) :
    (χ⁻¹ ^ j.val) v * χ v ^ 4 = (χ ^ (10 - j.val)) v := by
  have h6 := reflected_pow_six χ hχ v hv
  have hc : χ v ≠ 0 := MulChar.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr hv)
  have hp (n : ℕ) : (χ ^ n) v = χ v ^ n :=
    χ.pow_apply_coe n (Units.mk0 v hv)
  have hi (n : ℕ) : (χ⁻¹ ^ n) v = (χ v)⁻¹ ^ n := by
    simpa [MulChar.inv_apply_eq_inv'] using
      (χ⁻¹).pow_apply_coe n (Units.mk0 v hv)
  rw [hi, hp]
  fin_cases j <;> norm_num <;> field_simp <;>
    linear_combination -h6

private lemma reflected_positive_sum {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (hχ : orderOf χ = 6)
    (j : Fin 6) :
    (∑ v ∈ Finset.univ.erase (0 : k),
      sexticFourierMask χ ψ j v * χ v ^ 4) =
      if j.val = 4 then ((Fintype.card k : ℂ) - 1) / sexticMaskGaussSum χ ψ j
      else 0 := by
  classical
  by_cases hj0 : j.val = 0
  · have hj4 : j.val ≠ 4 := by omega
    simp only [if_neg hj4]
    have hsum : (∑ v ∈ Finset.univ.erase (0 : k), χ v ^ 4) = 0 := by
      have hzero : (χ ^ 4) (0 : k) = 0 := MulChar.map_zero _
      have h := MulChar.sum_eq_zero_of_ne_one (reflected_pow_ne_one χ hχ 4 (by norm_num))
      rw [← Finset.sum_erase Finset.univ hzero] at h
      simpa [MulChar.pow_apply' χ (by norm_num : (4 : ℕ) ≠ 0)] using h
    have hm (v : k) (hv : v ∈ Finset.univ.erase (0 : k)) :
        sexticFourierMask χ ψ j v * χ v ^ 4 =
          -(Fintype.card k : ℂ)⁻¹ * χ v ^ 4 := by
      simp [sexticFourierMask, hj0, Finset.ne_of_mem_erase hv]
    rw [Finset.sum_congr rfl hm]
    rw [← Finset.mul_sum, hsum, mul_zero]
  · have hrewrite (v : k) (hv : v ≠ 0) :
        sexticFourierMask χ ψ j v * χ v ^ 4 =
          (χ ^ (10 - j.val)) v / sexticMaskGaussSum χ ψ j := by
      simp only [sexticFourierMask, if_neg hj0, if_neg hv]
      rw [div_mul_eq_mul_div, reflected_twist χ hχ j v hv]
    rw [Finset.sum_congr rfl (fun v hv => hrewrite v (Finset.ne_of_mem_erase hv)),
      ← Finset.sum_div]
    by_cases hj4 : j.val = 4
    · simp only [if_pos hj4]
      have hn : 10 - j.val = 6 := by omega
      simp only [hn]
      have hchi6 : χ ^ 6 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
      simp only [hchi6]
      have hunit (v : k) (hv : v ≠ 0) : (1 : MulChar k ℂ) v = 1 :=
        MulChar.one_apply (isUnit_iff_ne_zero.mpr hv)
      simp_rw [Finset.sum_congr rfl (fun v hv => hunit v (Finset.ne_of_mem_erase hv))]
      simp [Nat.cast_sub (show 1 ≤ Fintype.card k by
        exact Fintype.card_pos), Finset.card_erase_of_mem]
    · simp only [if_neg hj4]
      have hn : ¬6 ∣ (10 - j.val) := by
        have hbound := j.isLt
        interval_cases j.val <;> norm_num at *
      have hzero : (χ ^ (10 - j.val)) (0 : k) = 0 := MulChar.map_zero _
      rw [Finset.sum_erase Finset.univ hzero,
        MulChar.sum_eq_zero_of_ne_one (reflected_pow_ne_one χ hχ _ hn)]
      simp

private lemma reflected_gauss_norm {k : Type*} [Field k] [Fintype k]
    (φ : MulChar k ℂ) (ψ : AddChar k ℂ) (hφ : φ ≠ 1)
    (hψ : ψ.IsPrimitive) :
    ‖gaussSum φ ψ‖ = Real.sqrt (Fintype.card k : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hφ hψ
  rw [← star_gaussSum_eq] at h
  have hnorm := congrArg norm h
  rw [norm_mul, norm_star, Complex.norm_natCast] at hnorm
  have hsqrt := Real.sq_sqrt (show 0 ≤ (Fintype.card k : ℝ) by positivity)
  nlinarith [norm_nonneg (gaussSum φ ψ), Real.sqrt_nonneg (Fintype.card k : ℝ)]

private lemma reflected_inverse_gauss {k : Type*} [Field k] [Fintype k]
    (φ : MulChar k ℂ) (ψ : AddChar k ℂ) (t : k) (ht : t ≠ 0) :
    (∑ v ∈ Finset.univ.erase (0 : k), φ v * ψ (t / v)) =
      φ t * gaussSum φ⁻¹ ψ := by
  classical
  have hz : (fun v : k => φ v * ψ (t / v)) 0 = 0 := by simp [MulChar.map_zero]
  rw [Finset.sum_erase (ι := k) (f := fun v : k => φ v * ψ (t / v)) Finset.univ hz]
  calc
    _ = ∑ v : k, φ⁻¹ v * ψ (t * v) := by
      refine Fintype.sum_bijective Inv.inv inv_involutive.bijective _ _ (fun v => ?_)
      simp [div_eq_mul_inv, MulChar.inv_apply']
    _ = gaussSum φ⁻¹ (ψ.mulShift t) := by simp [gaussSum, AddChar.mulShift_apply, mul_comm]
    _ = φ t * gaussSum φ⁻¹ ψ := by
      simpa using gaussSum_mulShift_eq φ⁻¹ ψ (Units.mk0 t ht)

private lemma reflected_inv_pow {k : Type*} [Field k] (χ : MulChar k ℂ)
    (hχ : orderOf χ = 6) (j : Fin 6) :
    (χ ^ (10 - j.val))⁻¹ = χ ^ ((j.val + 2) % 6) := by
  have h6 : χ ^ 6 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  apply inv_eq_of_mul_eq_one_left
  rw [← pow_add]
  have hn : (j.val + 2) % 6 + (10 - j.val) = 6 ∨
      (j.val + 2) % 6 + (10 - j.val) = 12 := by
    have := j.isLt
    interval_cases j.val <;> norm_num
  rcases hn with hn | hn
  · rw [hn, h6]
  · rw [hn, show 12 = 6 * 2 by omega, pow_mul, h6, one_pow]

private lemma reflected_phase {k : Type*} [Field k] (χ : MulChar k ℂ)
    (hχ : orderOf χ = 6) (j : Fin 6) (t : k) (ht : t ≠ 0) :
    χ t ^ 4 * (χ ^ (10 - j.val)) t = χ t ^ (8 - j.val) := by
  have hp : (χ ^ (10 - j.val)) t = χ t ^ (10 - j.val) :=
    χ.pow_apply_coe _ (Units.mk0 t ht)
  rw [hp, ← pow_add]
  have he : 4 + (10 - j.val) = (8 - j.val) + 6 := by have := j.isLt; omega
  rw [he, pow_add, reflected_pow_six χ hχ t ht, mul_one]

theorem sexticReflectedNonzeroDigits_depth_zero {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (hχ : orderOf χ = 6) (hψ : ψ.IsPrimitive)
    (hQ : Nat.Coprime (Fintype.card k) 6)
    (j : Fin 6) (t : k) (ht : t ≠ 0) :
    sexticReflectedNonzeroDigits χ ψ j 0 t =
      sexticReflectedDepthZeroScalar χ ψ j * (χ t) ^ (8 - j.val) := by
  have hs : sexticSphericalCoefficient χ ψ 0 = 1 := by
    norm_num [sexticSphericalCoefficient]
  simp only [sexticReflectedNonzeroDigits, hs, one_mul, mul_zero, add_zero,
    zpow_ofNat, if_pos rfl, ite_true]
  by_cases hj0 : j.val = 0
  · have hm (v : k) (hv : v ∈ Finset.univ.erase (0 : k)) :
        sexticFourierMask χ ψ j v * χ v ^ 4 * ψ (t / v) =
          -(Fintype.card k : ℂ)⁻¹ * ((χ ^ 4) v * ψ (t / v)) := by
      simp [sexticFourierMask, hj0, Finset.ne_of_mem_erase hv,
        MulChar.pow_apply' χ (by norm_num : (4 : ℕ) ≠ 0), mul_assoc]
    rw [Finset.sum_congr rfl hm, ← Finset.mul_sum, reflected_inverse_gauss _ ψ t ht]
    have h4inv : (χ ^ 4)⁻¹ = χ ^ 2 := by
      have h6 : χ ^ 6 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
      apply inv_eq_of_mul_eq_one_left
      rw [← pow_add]
      exact h6
    simp only [sexticReflectedDepthZeroScalar, if_pos hj0, h4inv, hj0, ite_true]
    rw [MulChar.pow_apply' χ (by norm_num : (4 : ℕ) ≠ 0)]
    ring
  · have hm (v : k) (hv : v ∈ Finset.univ.erase (0 : k)) :
        sexticFourierMask χ ψ j v * χ v ^ 4 * ψ (t / v) =
          ((χ ^ (10 - j.val)) v * ψ (t / v)) / sexticMaskGaussSum χ ψ j := by
      simp only [sexticFourierMask, if_neg hj0, if_neg (Finset.ne_of_mem_erase hv)]
      rw [div_mul_eq_mul_div, reflected_twist χ hχ j v (Finset.ne_of_mem_erase hv),
        div_mul_eq_mul_div]
    rw [Finset.sum_congr rfl hm, ← Finset.sum_div,
      reflected_inverse_gauss _ ψ t ht, reflected_inv_pow χ hχ j]
    simp only [sexticReflectedDepthZeroScalar, if_neg hj0]
    have hp := reflected_phase χ hχ j t ht
    calc
      _ = (χ t ^ 4 * (χ ^ (10 - j.val)) t) *
          (gaussSum (χ ^ ((j.val + 2) % 6)) ψ / sexticMaskGaussSum χ ψ j) := by ring
      _ = _ := by rw [hp]; ring

theorem sexticReflectedNonzeroDigits_eq_zero {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (hχ : orderOf χ = 6) (hψ : ψ.IsPrimitive)
    (hQ : Nat.Coprime (Fintype.card k) 6)
    (j : Fin 6) (e : ℤ) (t : k) (ht : t ≠ 0)
    (he : e < 0 ∨ e % 3 = 2 ∨ (0 < e ∧ j.val ≠ 4)) :
    sexticReflectedNonzeroDigits χ ψ j e t = 0 := by
  rcases he with he | he | ⟨he, hj⟩
  · simp [sexticReflectedNonzeroDigits, sexticSphericalCoefficient, he]
  · simp [sexticReflectedNonzeroDigits, sexticSphericalCoefficient,
      he, show ¬e % 3 = 0 by omega, show ¬e % 3 = 1 by omega]
  · simp only [sexticReflectedNonzeroDigits, if_neg (show e ≠ 0 by omega), mul_one]
    rw [reflected_positive_sum χ ψ hχ j, if_neg hj, mul_zero]

theorem sexticReflectedNonzeroDigits_positive {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (hχ : orderOf χ = 6) (hψ : ψ.IsPrimitive)
    (hQ : Nat.Coprime (Fintype.card k) 6)
    (e : ℤ) (he : 0 < e) (t : k) (ht : t ≠ 0) :
    sexticReflectedNonzeroDigits χ ψ 4 e t =
      sexticSphericalCoefficient χ ψ e * (χ t) ^ (4 + 2 * e) *
        ((Fintype.card k : ℂ) - 1) / sexticMaskGaussSum χ ψ 4 := by
  simp only [sexticReflectedNonzeroDigits, if_neg (show e ≠ 0 by omega), mul_one]
  rw [reflected_positive_sum χ ψ hχ 4]
  norm_num [mul_div_assoc]

theorem sexticReflectedDepthZeroScalar_norm_le {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (hχ : orderOf χ = 6) (hψ : ψ.IsPrimitive)
    (hQ : Nat.Coprime (Fintype.card k) 6) (j : Fin 6) :
    ‖sexticReflectedDepthZeroScalar χ ψ j‖ ≤ 1 := by
  have hcard : (1 : ℝ) ≤ Fintype.card k := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < Real.sqrt (Fintype.card k : ℝ) := Real.sqrt_pos.mpr (by positivity)
  by_cases hj : j.val = 0
  · have hn := reflected_gauss_norm (χ ^ 2) ψ
      (reflected_pow_ne_one χ hχ 2 (by norm_num)) hψ
    simp only [sexticReflectedDepthZeroScalar, if_pos hj, norm_mul, norm_neg,
      norm_inv, Complex.norm_natCast, hn]
    rw [← div_eq_inv_mul, div_le_one (by positivity)]
    have hs := Real.sq_sqrt (show 0 ≤ (Fintype.card k : ℝ) by positivity)
    nlinarith [Real.sqrt_nonneg (Fintype.card k : ℝ)]
  · have hd := sexticMaskGaussSum_norm χ ψ hχ hψ hQ j hj
    simp only [sexticReflectedDepthZeroScalar, if_neg hj, norm_div, hd]
    by_cases hj4 : j.val = 4
    · have hψne : ψ ≠ 1 := by simpa using hψ (one_ne_zero : (1 : k) ≠ 0)
      have hn : (j.val + 2) % 6 = 0 := by omega
      rw [hn, pow_zero, gaussSum_one_left hψne]
      simp only [norm_neg, norm_one]
      rw [div_le_one hpos]
      have hs := Real.sq_sqrt (show 0 ≤ (Fintype.card k : ℝ) by positivity)
      nlinarith [Real.sqrt_nonneg (Fintype.card k : ℝ)]
    · have hn : ¬6 ∣ ((j.val + 2) % 6) := by
        have hbound := j.isLt
        interval_cases j.val <;> norm_num at *
      rw [reflected_gauss_norm (χ ^ _) ψ (reflected_pow_ne_one χ hχ _ hn) hψ,
        div_self (ne_of_gt hpos)]

theorem sexticReflectedDigitModel_nonzero_mask {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (j : Fin 6) (hj : j.val ≠ 0)
    (e : ℤ) (t : k) :
    sexticReflectedDigitModel χ ψ j e t =
      sexticReflectedNonzeroDigits χ ψ j e t := by
  simp [sexticReflectedDigitModel, sexticFourierMask, hj]

end
end DedekindZetaZeroFree
