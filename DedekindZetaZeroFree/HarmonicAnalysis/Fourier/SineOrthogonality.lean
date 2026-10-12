module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/Analysis/SpecialFunctions/Trigonometric/Orthogonality.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

namespace DedekindZetaZeroFree.TauCeti

theorem integral_cos_int_mul (k : ℤ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cos ((k : ℝ) * θ) = if k = 0 then Real.pi else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have h := intervalIntegral.mul_integral_comp_mul_left
      (f := Real.cos) (a := (0 : ℝ)) (b := Real.pi) (k : ℝ)
    rw [integral_cos, mul_zero, Real.sin_zero, sub_zero, Real.sin_int_mul_pi] at h
    rw [ite_eq_right hk]
    exact (mul_eq_zero.mp h).resolve_left hk'

theorem integral_sin_nat_mul_mul_sin_nat_mul (m n : ℕ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin ((m : ℝ) * θ) * Real.sin ((n : ℝ) * θ)
      = if m = n ∧ m ≠ 0 then Real.pi / 2 else 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  ·
    simp
  rw [if_congr (and_iff_left hm) rfl rfl]

  have hprod : ∀ θ : ℝ, Real.sin ((m : ℝ) * θ) * Real.sin ((n : ℝ) * θ)
      = Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ) / 2
        - Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * θ) / 2 := by
    intro θ
    have hsub : (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ = (m : ℝ) * θ - (n : ℝ) * θ := by
      push_cast; ring
    have hadd : (((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * θ = (m : ℝ) * θ + (n : ℝ) * θ := by
      push_cast; ring
    rw [hsub, hadd, Real.cos_sub, Real.cos_add]
    ring
  have hint : ∀ k : ℤ, IntervalIntegrable (fun θ : ℝ => Real.cos ((k : ℝ) * θ) / 2)
      MeasureTheory.volume 0 Real.pi := fun k =>
    (by fun_prop : Continuous fun θ : ℝ => Real.cos ((k : ℝ) * θ) / 2).intervalIntegrable _ _
  have hne : (m : ℤ) + (n : ℤ) ≠ 0 := by omega
  simp only [hprod]
  rw [intervalIntegral.integral_sub (hint _) (hint _), intervalIntegral.integral_div,
    intervalIntegral.integral_div, integral_cos_int_mul, integral_cos_int_mul, ite_eq_right hne]
  rcases eq_or_ne m n with rfl | hmn
  · rw [ite_eq_left (by omega : (m : ℤ) - (m : ℤ) = 0), ite_eq_left rfl]
    ring
  · rw [ite_eq_right (by omega : ¬((m : ℤ) - (n : ℤ) = 0)), ite_eq_right hmn]
    ring

theorem integral_sin_succ_mul_sin_succ (m n : ℕ) :
    ∫ θ in (0 : ℝ)..Real.pi,
        Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ)
      = if m = n then Real.pi / 2 else 0 := by
  have hshift : ∀ θ : ℝ, Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ)
      = Real.sin (((m + 1 : ℕ) : ℝ) * θ) * Real.sin (((n + 1 : ℕ) : ℝ) * θ) := by
    intro θ; push_cast; ring
  simp only [hshift]
  rw [integral_sin_nat_mul_mul_sin_nat_mul (m + 1) (n + 1),
    if_congr (by omega : (m + 1 = n + 1 ∧ m + 1 ≠ 0) ↔ m = n) rfl rfl]

theorem two_div_pi_mul_integral_sin_succ_mul_sin_succ (m n : ℕ) :
    2 / Real.pi * ∫ θ in (0 : ℝ)..Real.pi,
        Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ)
      = if m = n then 1 else 0 := by
  rw [integral_sin_succ_mul_sin_succ]
  rcases eq_or_ne m n with rfl | hmn
  · rw [ite_eq_left rfl, ite_eq_left rfl]
    field_simp
  · rw [ite_eq_right hmn, ite_eq_right hmn]
    ring

end DedekindZetaZeroFree.TauCeti
