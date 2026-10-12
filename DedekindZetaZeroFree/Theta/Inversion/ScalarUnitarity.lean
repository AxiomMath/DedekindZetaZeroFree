module

public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

theorem thetaInversionScalar_norm_eq_one (f : ℝ → ℂ) (w : ℂ)
    (hinversion : ∀ t : ℝ, 0 < t →
      f t = w * (t : ℂ)⁻¹ * (starRingEnd ℂ) (f t⁻¹))
    (hnonzero : ∃ t : ℝ, 0 < t ∧ f t ≠ 0) :
    ‖w‖ = 1 := by
  obtain ⟨t, ht, hft⟩ := hnonzero
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  have h1 := hinversion t ht
  have h2 := hinversion t⁻¹ (inv_pos.mpr ht)

  have h2' : f t⁻¹ = w * (t : ℂ) * (starRingEnd ℂ) (f t) := by
    rw [h2]
    have hc : ((t⁻¹ : ℝ) : ℂ)⁻¹ = (t : ℂ) := by
      rw [Complex.ofReal_inv, inv_inv]
    rw [hc, inv_inv]

  have h3 : (starRingEnd ℂ) (f t⁻¹) = (starRingEnd ℂ) w * (t : ℂ) * f t := by
    rw [h2']
    simp

  have h4 : f t = (w * (starRingEnd ℂ) w) * f t := by
    calc f t = w * (t : ℂ)⁻¹ * (starRingEnd ℂ) (f t⁻¹) := h1
      _ = w * (t : ℂ)⁻¹ * ((starRingEnd ℂ) w * (t : ℂ) * f t) := by rw [h3]
      _ = (w * (starRingEnd ℂ) w) * f t := by
            field_simp

  have hw : w * (starRingEnd ℂ) w = 1 := by
    have h5 : (w * (starRingEnd ℂ) w) * f t = 1 * f t := by rw [← h4, one_mul]
    exact mul_right_cancel₀ hft h5

  have hnorm : ‖w‖ ^ 2 = 1 := by
    have h := congrArg (fun z : ℂ => ‖z‖) hw
    simp only [norm_mul, norm_one] at h
    rw [starRingEnd_apply, norm_star] at h
    rwa [pow_two]
  rcases sq_eq_one_iff.mp hnorm with h | h
  · exact h
  · exfalso
    have := norm_nonneg w
    rw [h] at this
    norm_num at this

end DedekindZetaZeroFree.Hecke
