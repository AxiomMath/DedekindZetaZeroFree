module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RingTheory/LocalRing/Basic.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

namespace DedekindZetaZeroFree.TauCeti

theorem IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem {R : Type*} [Ring R] [IsLocalRing R]
    {a : R} (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  have hsum : IsUnit (a + (1 - a)) := by simp
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with hu | hu
  · exact Or.inr (hu.mul_left_cancel (by rw [ha, mul_one]))
  · refine Or.inl ?_
    have hidem : IsIdempotentElem (1 - a) := IsIdempotentElem.one_sub ha
    have hone : (1 : R) - a = 1 := hu.mul_left_cancel (by rw [hidem, mul_one])
    exact sub_eq_self.mp hone

instance IsLocalRing.isDedekindFiniteMonoid {R : Type*} [Ring R] [IsLocalRing R] :
    IsDedekindFiniteMonoid R where
  mul_eq_one_symm := by
    intro p q hpq
    have he : IsIdempotentElem (q * p) := by
      rw [IsIdempotentElem]
      calc
        (q * p) * (q * p) = q * (p * q) * p := by simp only [mul_assoc]
        _ = q * p := by rw [hpq, mul_one]
    rcases IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem he with h0 | h1
    · have hp0 : p = 0 := by
        calc
          p = (p * q) * p := by rw [hpq, one_mul]
          _ = p * (q * p) := by rw [mul_assoc]
          _ = 0 := by rw [h0, mul_zero]
      simpa only [hp0, mul_zero, zero_mul] using hpq
    · exact h1

@[simp]
theorem IsLocalRing.sq_add_self_eq_zero_iff {R : Type*} [Ring R] [IsLocalRing R] [CharP R 2]
    (t : R) : t ^ 2 + t = 0 ↔ t = 0 ∨ t = 1 := by
  rw [CharTwo.add_eq_zero, pow_two]
  constructor
  · exact IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem
  · rintro (rfl | rfl) <;> simp

end DedekindZetaZeroFree.TauCeti
