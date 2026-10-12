module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.LocalSeriesDefinitions

@[expose] public section

namespace DedekindZetaZeroFree.FiniteGaussTable

variable {κ : Type*} [Field κ] [Fintype κ]

noncomputable def T (χ : MulChar κ ℂ) (ψ : AddChar κ ℂ)
    (a : ℕ) (y : κ) : ℂ :=
  ∑ x : κ, (χ ^ a) x * ψ (y * x)

noncomputable def tau (χ : MulChar κ ℂ) (ψ : AddChar κ ℂ) (a : ℕ) : ℂ :=
  T χ ψ a 1

theorem characterPower_mask (χ : MulChar κ ℂ) (a : ℕ) :
    (χ ^ a) (0 : κ) = 0 ∧ ∀ x : κ, x ≠ 0 → (χ ^ a) x = χ x ^ a := by
  constructor
  · exact MulChar.map_zero _
  · intro x hx
    simpa using χ.pow_apply_coe a (Units.mk0 x hx)

theorem T_zero (χ : MulChar κ ℂ) (ψ : AddChar κ ℂ)
    (hχ : orderOf χ = 6) (hψ : ψ ≠ 1) (a : ℕ) :
    T χ ψ a 0 = if 6 ∣ a then (Fintype.card κ : ℂ) - 1 else 0 := by
  classical
  have hp : χ ^ a = 1 ↔ 6 ∣ a := by
    rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  simp only [T, zero_mul, AddChar.map_zero_eq_one, mul_one]
  split_ifs with ha
  · rw [hp.mpr ha, MulChar.sum_one_eq_card_units, Fintype.card_units]
    rw [Nat.cast_sub (Nat.succ_le_of_lt Fintype.card_pos), Nat.cast_one]
  · exact MulChar.sum_eq_zero_of_ne_one (fun h => ha (hp.mp h))

theorem T_ne_zero (χ : MulChar κ ℂ) (ψ : AddChar κ ℂ)
    (hχ : orderOf χ = 6) (hψ : ψ ≠ 1) (a : ℕ) (y : κ) (hy : y ≠ 0) :
    T χ ψ a y = star (χ y) ^ a * tau χ ψ a := by
  classical
  have h := gaussSum_mulShift_eq (χ ^ a) ψ (Units.mk0 y hy)
  simpa [T, tau, gaussSum, AddChar.mulShift_apply,
    ← MulChar.star_apply', characterPower_mask χ a |>.2 y hy, star_pow] using h

theorem norm_tau_of_not_six_dvd (χ : MulChar κ ℂ) (ψ : AddChar κ ℂ)
    (hχ : orderOf χ = 6) (hψ : ψ ≠ 1) (a : ℕ) (ha : ¬6 ∣ a) :
    ‖tau χ ψ a‖ = Real.sqrt (Fintype.card κ) := by
  have hp : χ ^ a ≠ 1 := by
    intro h
    exact ha (hχ ▸ orderOf_dvd_of_pow_eq_one h)
  have h := gaussSum_mul_gaussSum_eq_card hp (AddChar.IsPrimitive.of_ne_one hψ)
  rw [← star_gaussSum_eq, Complex.star_def, Complex.mul_conj'] at h
  have hs : ‖tau χ ψ a‖ ^ 2 = (Fintype.card κ : ℝ) := by
    exact_mod_cast (show ‖tau χ ψ a‖ ^ 2 = (Fintype.card κ : ℂ) by
      simpa [tau, T, gaussSum] using h)
  exact ((Real.sqrt_eq_iff_eq_sq (by positivity) (norm_nonneg _)).mpr hs.symm).symm

end DedekindZetaZeroFree.FiniteGaussTable
