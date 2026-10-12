module

public import Mathlib.RingTheory.Polynomial.ShiftedLegendre

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke.CircleAverage

open Polynomial

def Lc (ℓ k : ℕ) : ℤ := (-1) ^ k * (ℓ.choose k : ℤ) * ((ℓ + k).choose ℓ : ℤ)

private lemma Lc_rec (ℓ k : ℕ) :
    ((k + 1 : ℤ) ^ 2) * Lc ℓ (k + 1)
      = ((k : ℤ) * ((k + 1 : ℕ) : ℤ) - (ℓ : ℤ) * ((ℓ : ℤ) + 1)) * Lc ℓ k := by
  by_cases hk : k < ℓ
  · have h1 : (ℓ.choose (k + 1) : ℤ) * ((k + 1 : ℕ) : ℤ)
        = (ℓ.choose k : ℤ) * ((ℓ - k : ℕ) : ℤ) := by
      exact_mod_cast (Nat.choose_succ_right_eq ℓ k)
    have h2 : ((ℓ + (k + 1)).choose ℓ : ℤ) * ((k + 1 : ℕ) : ℤ)
        = ((ℓ + k).choose ℓ : ℤ) * ((ℓ + (k + 1) : ℕ) : ℤ) := by
      have h := Nat.choose_mul_succ_eq (ℓ + k) ℓ
      have e2 : ℓ + k + 1 - ℓ = k + 1 := by omega
      rw [e2] at h
      have e1 : ℓ + k + 1 = ℓ + (k + 1) := by omega
      rw [e1] at h
      exact_mod_cast h.symm
    have hkey : (k : ℤ) * ((k + 1 : ℕ) : ℤ) - (ℓ : ℤ) * ((ℓ : ℤ) + 1)
        = -(((ℓ - k : ℕ) : ℤ) * ((ℓ + (k + 1) : ℕ) : ℤ)) := by
      rw [Nat.cast_sub (le_of_lt hk)]
      push_cast
      ring
    have hXY : ((k + 1 : ℤ) ^ 2) * ((ℓ.choose (k + 1) : ℤ) * ((ℓ + (k + 1)).choose ℓ : ℤ))
        = (ℓ.choose k : ℤ) * ((ℓ + k).choose ℓ : ℤ)
          * (((ℓ - k : ℕ) : ℤ) * ((ℓ + (k + 1) : ℕ) : ℤ)) := by
      rw [show ((k + 1 : ℤ) ^ 2) * ((ℓ.choose (k + 1) : ℤ) * ((ℓ + (k + 1)).choose ℓ : ℤ))
            = ((ℓ.choose (k + 1) : ℤ) * ((k + 1 : ℕ) : ℤ))
              * (((ℓ + (k + 1)).choose ℓ : ℤ) * ((k + 1 : ℕ) : ℤ)) by push_cast; ring,
        h1, h2]
      ring
    have hp : (-1 : ℤ) ^ (k + 1) = -((-1 : ℤ) ^ k) := by rw [pow_succ]; ring
    simp only [Lc]
    rw [show ((k + 1 : ℤ) ^ 2)
            * ((-1) ^ (k + 1) * (ℓ.choose (k + 1) : ℤ) * ((ℓ + (k + 1)).choose ℓ : ℤ))
          = (-1) ^ (k + 1)
            * (((k + 1 : ℤ) ^ 2) * ((ℓ.choose (k + 1) : ℤ) * ((ℓ + (k + 1)).choose ℓ : ℤ)))
          by ring,
      hXY, hp, hkey]
    ring
  · have hA1 : Lc ℓ (k + 1) = 0 := by
      simp only [Lc]
      have : ℓ.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [this]
    rw [hA1, mul_zero]
    rcases eq_or_lt_of_le (not_lt.mp hk) with h | h
    · subst h
      simp only [Lc]
      push_cast
      ring
    · have : ℓ.choose k = 0 := Nat.choose_eq_zero_of_lt h
      simp [Lc, this]

private lemma coeff_op {K : Type*} [Field K] (c : K) (R : Polynomial K) (k : ℕ) :
    (Polynomial.derivative (Polynomial.X * (1 - Polynomial.X) * R.derivative) +
      Polynomial.C c * R).coeff k
    = ((k + 1 : ℕ) : K) ^ 2 * R.coeff (k + 1)
      - (((k : ℕ) : K) * ((k + 1 : ℕ) : K) - c) * R.coeff k := by
  rcases k with _ | m
  · have e : Polynomial.X * (1 - Polynomial.X) * R.derivative
        = Polynomial.X * R.derivative - Polynomial.X ^ 2 * R.derivative := by ring
    rw [e]
    simp only [coeff_add, coeff_sub, coeff_derivative, coeff_C_mul, pow_two, mul_assoc,
      coeff_X_mul, coeff_X_mul_zero, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, mul_one,
      mul_zero, sub_zero, zero_add]
    ring
  · have e : Polynomial.X * (1 - Polynomial.X) * R.derivative
        = Polynomial.X * R.derivative - Polynomial.X ^ 2 * R.derivative := by ring
    rw [e]
    simp only [coeff_add, coeff_sub, coeff_derivative, coeff_C_mul, pow_two, mul_assoc,
      coeff_X_mul, Nat.cast_add, Nat.cast_one, add_mul, mul_add]
    ring

theorem polynomial_shiftedLegendre_ode_unique {K : Type*} [Field K] [CharZero K]
    (ℓ : ℕ) (Q : Polynomial K)
    (hQ : Polynomial.X * (1 - Polynomial.X) * Q.derivative.derivative +
      (1 - 2 * Polynomial.X) * Q.derivative +
      Polynomial.C ((ℓ : K) * ((ℓ : K) + 1)) * Q = 0) :
    Q = Polynomial.C (Q.eval 0) *
      (Polynomial.shiftedLegendre ℓ).map (Int.castRingHom K) := by
  set P : Polynomial K := (Polynomial.shiftedLegendre ℓ).map (Int.castRingHom K) with hP
  have hop : Polynomial.X * (1 - Polynomial.X) * Q.derivative.derivative +
        (1 - 2 * Polynomial.X) * Q.derivative
      = Polynomial.derivative (Polynomial.X * (1 - Polynomial.X) * Q.derivative) := by
    simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_one,
      Polynomial.derivative_X, Polynomial.derivative_C]
    ring
  have hQrec : ∀ k, ((k + 1 : ℕ) : K) ^ 2 * Q.coeff (k + 1)
      = (((k : ℕ) : K) * ((k + 1 : ℕ) : K) - (ℓ : K) * ((ℓ : K) + 1)) * Q.coeff k := by
    intro k
    have h := congrArg (fun p : Polynomial K => p.coeff k) hQ
    rw [hop] at h
    simp only [coeff_zero] at h
    rw [coeff_op] at h
    exact sub_eq_zero.mp h
  have hPcoeff : ∀ j, P.coeff j = (Lc ℓ j : K) := by
    intro j
    rw [hP, Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre]
    simp only [Lc, Int.coe_castRingHom]
  have hPrec : ∀ k, ((k + 1 : ℕ) : K) ^ 2 * P.coeff (k + 1)
      = (((k : ℕ) : K) * ((k + 1 : ℕ) : K) - (ℓ : K) * ((ℓ : K) + 1)) * P.coeff k := by
    intro k
    rw [hPcoeff (k + 1), hPcoeff k]
    exact_mod_cast Lc_rec ℓ k
  have hcoeff : ∀ k, Q.coeff k = Q.coeff 0 * P.coeff k := by
    intro k
    induction k with
    | zero => rw [hPcoeff 0]; simp [Lc]
    | succ n ih =>
      have h1 := hQrec n
      have h2 := hPrec n
      rw [ih] at h1
      have hne : (((n + 1 : ℕ)) : K) ^ 2 ≠ 0 := by
        have : ((n + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        positivity
      have key : (((n + 1 : ℕ)) : K) ^ 2 * Q.coeff (n + 1)
          = (((n + 1 : ℕ)) : K) ^ 2 * (Q.coeff 0 * P.coeff (n + 1)) := by
        have e1 : (((n + 1 : ℕ)) : K) ^ 2 * (Q.coeff 0 * P.coeff (n + 1))
            = Q.coeff 0 * ((((n + 1 : ℕ)) : K) ^ 2 * P.coeff (n + 1)) := by ring
        rw [e1, h2, h1]
        ring
      exact mul_left_cancel₀ hne key
  have hQeq : Q = Polynomial.C (Q.coeff 0) * P := by
    ext k
    rw [hcoeff k]
    simp [Polynomial.coeff_C_mul]
  exact hQeq.trans (by rw [Polynomial.coeff_zero_eq_eval_zero])

end DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke.CircleAverage
