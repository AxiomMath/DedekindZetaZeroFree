module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.SymmetricPower
public import DedekindZetaZeroFree.Geometry.Circle.ArcAndChord

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/SU2/Weyl/Character.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open Finset

namespace DedekindZetaZeroFree.TauCeti

namespace SU2

variable (d : ℕ)

theorem sub_inv_mul_character_symPower_torusHom (z : Circle) :
    ((z : ℂ) - (z : ℂ)⁻¹) * (symPower d).character (torusHom z)
      = (z : ℂ) ^ (d + 1) - ((z : ℂ)⁻¹) ^ (d + 1) := by
  have hz : (z : ℂ) ≠ 0 := z.coe_ne_zero
  rw [character_symPower_torusHom_zpow, mul_sum]
  have key : ∀ i ∈ range (d + 1),
      ((z : ℂ) - (z : ℂ)⁻¹) * (z : ℂ) ^ (2 * (i : ℤ) - d)
        = (z : ℂ) ^ (2 * ((i + 1 : ℕ) : ℤ) - d - 1) - (z : ℂ) ^ (2 * (i : ℤ) - d - 1) := by
    intro i _
    have hsplit : (z : ℂ) - (z : ℂ)⁻¹ = (z : ℂ) ^ (1 : ℤ) - (z : ℂ) ^ (-1 : ℤ) := by
      simp
    rw [hsplit, sub_mul, ← zpow_add₀ hz, ← zpow_add₀ hz]
    congr 2 <;> push_cast <;> ring
  rw [sum_congr rfl key, sum_range_sub (fun j : ℕ => (z : ℂ) ^ (2 * (j : ℤ) - d - 1)) (d + 1),
    inv_pow, ← zpow_natCast (z : ℂ) (d + 1)]
  have hbot : (0 : ℤ) - (d : ℤ) - 1 = -((d : ℤ) + 1) := by ring
  have htop : 2 * ((d : ℤ) + 1) - (d : ℤ) - 1 = (d : ℤ) + 1 := by ring
  push_cast
  rw [hbot, zpow_neg, htop]

theorem character_symPower_torusHom_of_sq_eq_one {z : Circle} (hz : (z : ℂ) ^ 2 = 1) :
    (symPower d).character (torusHom z) = ((d : ℂ) + 1) * (z : ℂ) ^ d := by
  have hz0 : (z : ℂ) ≠ 0 := z.coe_ne_zero
  have hpow : ((z : ℂ) ^ d) * ((z : ℂ) ^ d) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, hz, one_pow]
  rw [character_symPower_torusHom_zpow]
  have hterm : ∀ i ∈ range (d + 1), (z : ℂ) ^ (2 * (i : ℤ) - d) = (z : ℂ) ^ d := by
    intro i _
    have hsq : (z : ℂ) ^ (2 : ℤ) = 1 := by
      rw [zpow_two, ← pow_two]
      exact hz
    have h2 : (z : ℂ) ^ (2 * (i : ℤ)) = 1 := by
      rw [zpow_mul, hsq, one_zpow]
    rw [zpow_sub₀ hz0, h2, zpow_natCast, one_div, eq_comm]
    exact eq_inv_of_mul_eq_one_left hpow
  rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

private theorem exp_sub_exp_neg_mul_I (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) - Complex.exp (-((t : ℂ) * Complex.I))
      = 2 * Complex.I * (Real.sin t : ℂ) := by
  have h := exp_mul_I_sub_exp_mul_I t (-t)
  simp only [Complex.ofReal_neg, neg_mul, sub_neg_eq_add, add_self_div_two, add_neg_cancel,
    zero_div, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at h
  rw [h]
  ring

theorem sin_mul_character_symPower_torusExp (θ : ℝ) :
    (Real.sin θ : ℂ) * (symPower d).character (torusExp θ)
      = (Real.sin (((d : ℝ) + 1) * θ) : ℂ) := by
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.I_ne_zero]
  refine mul_left_cancel₀ hI ?_
  have hz : ((Circle.exp θ : Circle) : ℂ) = Complex.exp ((θ : ℂ) * Complex.I) :=
    Circle.coe_exp θ
  have hden : ((Circle.exp θ : Circle) : ℂ) - ((Circle.exp θ : Circle) : ℂ)⁻¹
      = 2 * Complex.I * (Real.sin θ : ℂ) := by
    rw [hz, ← Complex.exp_neg, exp_sub_exp_neg_mul_I]
  have h₁ : ((d : ℂ) + 1) * ((θ : ℂ) * Complex.I)
      = ((((d : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have h₂ : ((d : ℂ) + 1) * -((θ : ℂ) * Complex.I)
      = -(((((d : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  have hnum : ((Circle.exp θ : Circle) : ℂ) ^ (d + 1)
      - (((Circle.exp θ : Circle) : ℂ)⁻¹) ^ (d + 1)
      = 2 * Complex.I * (Real.sin (((d : ℝ) + 1) * θ) : ℂ) := by
    rw [hz, ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Nat.cast_add,
      Nat.cast_one, h₁, h₂, exp_sub_exp_neg_mul_I]
  rw [torusExp_def, ← mul_assoc, ← hden, sub_inv_mul_character_symPower_torusHom d (Circle.exp θ)]
  exact hnum

theorem character_symPower_torusExp_eq_sin_div_sin {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    (symPower d).character (torusExp θ)
      = ((Real.sin (((d : ℝ) + 1) * θ) / Real.sin θ : ℝ) : ℂ) := by
  have hθ' : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast hθ
  rw [Complex.ofReal_div, eq_div_iff hθ', mul_comm]
  exact sin_mul_character_symPower_torusExp d θ

theorem character_symPower_torusExp_of_sin_eq_zero {θ : ℝ} (hθ : Real.sin θ = 0) :
    (symPower d).character (torusExp θ) = ((d : ℂ) + 1) * (Real.cos θ : ℂ) ^ d := by
  have hz : ((Circle.exp θ : Circle) : ℂ) = (Real.cos θ : ℂ) := by
    rw [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hθ]
    simp
  have hcos : Real.cos θ ^ 2 = 1 := by
    have hpyth := Real.sin_sq_add_cos_sq θ
    rw [hθ] at hpyth
    simpa using hpyth
  have hsq : ((Circle.exp θ : Circle) : ℂ) ^ 2 = 1 := by
    rw [hz, ← Complex.ofReal_pow, hcos, Complex.ofReal_one]
  rw [torusExp_def, character_symPower_torusHom_of_sq_eq_one d hsq, hz]

@[simp]
theorem conj_character_symPower_torusExp (θ : ℝ) :
    (starRingEnd ℂ) ((symPower d).character (torusExp θ))
      = (symPower d).character (torusExp θ) := by
  rcases eq_or_ne (Real.sin θ) 0 with hθ | hθ
  · rw [character_symPower_torusExp_of_sin_eq_zero d hθ]
    simp only [map_mul, map_pow, map_add, map_one, map_natCast, Complex.conj_ofReal]
  · rw [character_symPower_torusExp_eq_sin_div_sin d hθ, Complex.conj_ofReal]

end SU2

end DedekindZetaZeroFree.TauCeti
