module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Vendor

theorem inverse_Gammaℂ_recurrence (s : ℂ) :
    (Complex.Gammaℂ s)⁻¹ =
      (s / (2 * (Real.pi : ℂ))) * (Complex.Gammaℂ (s + 1))⁻¹ := by
  have hA : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [Complex.Gammaℂ_def, Complex.Gammaℂ_def]
  simp only [mul_inv]
  rw [Complex.cpow_neg, inv_inv, Complex.cpow_neg, inv_inv,
    Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s,
    Complex.cpow_add s 1 hA, Complex.cpow_one]
  set G : ℂ := (Complex.Gamma (s + 1))⁻¹
  rw [div_eq_mul_inv]
  field_simp

theorem Gammaℂ_add_nat_rising_product (s : ℂ) (n : ℕ) (hs : s.im ≠ 0) :
    Complex.Gammaℂ (s + (n : ℂ)) =
      Complex.Gammaℂ s * (∏ j ∈ Finset.range n, (s + (j : ℂ))) /
        (2 * (Real.pi : ℂ)) ^ n := by
  have hA : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero]
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : s + (n : ℂ) ≠ 0 := by
      intro h
      apply hs
      have := congrArg Complex.im h
      simpa using this
    rw [show s + ((n + 1 : ℕ) : ℂ) = (s + (n : ℂ)) + 1 by push_cast; ring,
      Complex.Gammaℂ_add_one hne, ih, Finset.prod_range_succ, pow_succ]
    field_simp

theorem rising_product_norm_lower_bound (σ t : ℝ) (n : ℕ) (ht : 1 ≤ |t|) :
    |t| ^ n ≤
      ‖∏ j ∈ Finset.range n, ((σ : ℂ) + (t : ℂ) * Complex.I + (j : ℂ))‖ := by
  have hnorm : ∀ j ∈ Finset.range n,
      |t| ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (j : ℂ)‖ := by
    intro j _
    have h := Complex.abs_im_le_norm ((σ : ℂ) + (t : ℂ) * Complex.I + (j : ℂ))
    rwa [show ((σ : ℂ) + (t : ℂ) * Complex.I + (j : ℂ)).im = t by
      simp [Complex.add_im, Complex.mul_I_im]] at h
  rw [Complex.norm_prod]
  calc |t| ^ n = ∏ _j ∈ Finset.range n, |t| := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ j ∈ Finset.range n, ‖(σ : ℂ) + (t : ℂ) * Complex.I + (j : ℂ)‖ :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg t) hnorm

end DedekindZetaZeroFree.LargeSieve.Vendor
