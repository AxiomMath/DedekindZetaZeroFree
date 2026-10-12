module

public import DedekindZetaZeroFree.Moments.Principal.Corrections.Definitions
public import DedekindZetaZeroFree.Moments.Principal.EulerCorrectionAlgebra

@[expose] public section

open scoped NumberField Classical

noncomputable section
namespace DedekindZetaZeroFree.CorrectionFactors
set_option autoImplicit false

open LocalFiniteSums

def localPrincipalRegion : Set ℂ := {s | (1 / 2 : ℝ) < s.re}

def principalModel (Q : ℝ) (α β : ℂ) (s : ℂ) : ℂ :=
  Audit.Euler.principalCorrection (Q : ℂ)⁻¹
    (α * Complex.exp (-s * (Real.log Q : ℂ)))
    (β * Complex.exp ((3 - 6 * s) * (Real.log Q : ℂ)))

def principalGap (σ₀ : ℝ) : ℝ :=
  1 - max (Real.rpow 2 (-σ₀)) (Real.rpow 2 (3 - 6 * σ₀))

theorem principalGap_pos (σ₀ : ℝ) (hσ₀ : (1 / 2 : ℝ) < σ₀) :
    0 < principalGap σ₀ := by
  unfold principalGap
  have h₁ : Real.rpow 2 (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h₂ : Real.rpow 2 (3 - 6 * σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact sub_pos.mpr (max_lt h₁ h₂)

private lemma model_moduli (σ₀ Q : ℝ) (hσ₀ : (1 / 2 : ℝ) < σ₀)
    (hQ : 2 ≤ Q) (α β s : ℂ) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    (hs : σ₀ ≤ s.re) :
    ‖α * Complex.exp (-s * (Real.log Q : ℂ))‖ ≤ 1 - principalGap σ₀ ∧
    ‖β * Complex.exp ((3 - 6 * s) * (Real.log Q : ℂ))‖ ≤ 1 - principalGap σ₀ := by
  have hQ0 : 0 < Q := by linarith
  have hn (z : ℂ) : ‖Complex.exp (z * (Real.log Q : ℂ))‖ = Real.rpow Q z.re := by
    rw [Complex.norm_exp, Real.rpow_eq_pow, Real.rpow_def_of_pos hQ0]
    simp [mul_comm]
  simp only [norm_mul, hα, hβ, one_mul, hn]
  have hre : (3 - 6 * s).re = 3 - 6 * s.re := by simp
  rw [Complex.neg_re, hre]
  have hd : Real.rpow Q (-s.re) ≤ Real.rpow 2 (-σ₀) :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg hs)).trans
      (Real.rpow_le_rpow_of_nonpos (by norm_num) hQ (by linarith))
  have he : Real.rpow Q (3 - 6 * s.re) ≤ Real.rpow 2 (3 - 6 * σ₀) :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans
      (Real.rpow_le_rpow_of_nonpos (by norm_num) hQ (by linarith))
  constructor
  · simpa [principalGap] using hd.trans (le_max_left _ _)
  · simpa [principalGap] using he.trans (le_max_right _ _)

private lemma rational_bounds (r M : ℝ) (D E : ℂ) (hr0 : 0 ≤ r)
    (hr : r ≤ 1 / 2) (hM : M < 1) (hD : ‖D‖ ≤ M) (hE : ‖E‖ ≤ M) :
    3 * (1 - M) / 16 ≤ ‖Audit.Euler.principalCorrection (r : ℂ) D E‖ ∧
      1 - M ≤ ‖1 - E‖ ∧ 1 - M ≤ ‖1 - D‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg D).trans hD
  have hdn : 1 - M ≤ ‖1 - D‖ := by
    have := norm_sub_norm_le (1 : ℂ) D
    simp only [norm_one] at this
    linarith
  have hen : 1 - M ≤ ‖1 - E‖ := by
    have := norm_sub_norm_le (1 : ℂ) E
    simp only [norm_one] at this
    linarith
  have hw : ‖(1 - (r : ℂ)) * D + (r : ℂ) * E‖ ≤ M := by
    calc
      _ ≤ ‖(1 - (r : ℂ)) * D‖ + ‖(r : ℂ) * E‖ := norm_add_le _ _
      _ = (1 - r) * ‖D‖ + r * ‖E‖ := by
        rw [norm_mul, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub]
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hr0, abs_of_nonneg (show 0 ≤ 1 - r by linarith)]
      _ ≤ (1 - r) * M + r * M := by gcongr <;> linarith
      _ = M := by ring
  have hn : 1 - M ≤ ‖1 - (1 - (r : ℂ)) * D - (r : ℂ) * E‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((1 - (r : ℂ)) * D + (r : ℂ) * E)
    rw [norm_one] at this
    rw [sub_sub]
    linarith
  have hc : (3 / 4 : ℝ) ≤ ‖1 - (r : ℂ) ^ 2‖ := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ 1 - r ^ 2 by nlinarith)]
    nlinarith
  have hdu : ‖1 - D‖ ≤ 2 := (norm_sub_le _ _).trans (by simpa using (show 1 + ‖D‖ ≤ 2 by linarith))
  have heu : ‖1 - E‖ ≤ 2 := (norm_sub_le _ _).trans (by simpa using (show 1 + ‖E‖ ≤ 2 by linarith))
  have hden : 0 < ‖1 - E‖ * ‖1 - D‖ := mul_pos (by linarith) (by linarith)
  have hdenu : ‖1 - E‖ * ‖1 - D‖ ≤ 4 := by nlinarith [norm_nonneg (1 - E), norm_nonneg (1 - D)]
  refine ⟨?_, hen, hdn⟩
  unfold Audit.Euler.principalCorrection
  rw [norm_div, norm_mul, norm_mul]
  apply (le_div_iff₀ hden).mpr
  have hnum : (3 / 4 : ℝ) * (1 - M) ≤ ‖1 - (r : ℂ) ^ 2‖ *
      ‖1 - (1 - (r : ℂ)) * D - (r : ℂ) * E‖ := by gcongr
  nlinarith

theorem principalModel_uniform_lower_bounds
    (σ₀ : ℝ) (hσ₀ : (1 / 2 : ℝ) < σ₀)
    (Q : ℝ) (hQ : 2 ≤ Q) (α β : ℂ) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    (s : ℂ) (hs : σ₀ ≤ s.re) :
    3 * principalGap σ₀ / 16 ≤ ‖principalModel Q α β s‖ ∧
      principalGap σ₀ ≤ ‖1 - β * Complex.exp ((3 - 6 * s) * (Real.log Q : ℂ))‖ ∧
      principalGap σ₀ ≤ ‖1 - α * Complex.exp (-s * (Real.log Q : ℂ))‖ := by
  obtain ⟨hd, he⟩ := model_moduli σ₀ Q hσ₀ hQ α β s hα hβ hs
  have hg := principalGap_pos σ₀ hσ₀
  have hr : Q⁻¹ ≤ 1 / 2 := by
    simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hQ)
  simpa [principalModel] using rational_bounds Q⁻¹ (1 - principalGap σ₀)
    (α * Complex.exp (-s * (Real.log Q : ℂ)))
    (β * Complex.exp ((3 - 6 * s) * (Real.log Q : ℂ)))
    (inv_nonneg.mpr (by linarith)) hr (by linarith) hd he

end DedekindZetaZeroFree.CorrectionFactors

end
