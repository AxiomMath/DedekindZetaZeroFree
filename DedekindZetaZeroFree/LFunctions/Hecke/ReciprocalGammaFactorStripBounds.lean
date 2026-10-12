module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.Real.Pi.Bounds
public import DedekindZetaZeroFree.Analysis.Gamma.ElementaryNormBounds

@[expose] public section

namespace DedekindZetaZeroFree

private lemma gamma_inv_reflection {s : ℂ} (hs : s.im ≠ 0) :
    (Complex.Gamma s)⁻¹ = Complex.Gamma (1 - s) * Complex.sin (Real.pi * s) / Real.pi := by
  have hGam : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero (fun m hm => hs (by rw [hm]; simp))
  have hGam1 : Complex.Gamma (1 - s) ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m hm => ?_)
    have : (1 - s).im = 0 := by rw [hm]; simp
    simp [Complex.sub_im] at this
    exact hs this
  have h := Complex.Gamma_mul_Gamma_one_sub s
  have hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at h
    exact mul_ne_zero hGam hGam1 h
  have h2 : Complex.Gamma (1 - s) =
      (Complex.Gamma s)⁻¹ * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s)) := by
    have := congrArg (fun x => (Complex.Gamma s)⁻¹ * x) h
    rw [← mul_assoc, inv_mul_cancel₀ hGam, one_mul] at this
    exact this
  rw [h2]
  field_simp

theorem gamma_inverse_strip_exp_bound (a b : ℝ) (hab : a ≤ b) :
    ∃ G : ℝ, 0 < G ∧ ∀ s : ℂ, a ≤ s.re ∧ s.re ≤ b →
      ‖(Complex.Gamma s)⁻¹‖ ≤ G * Real.exp (Real.pi * |s.im|) := by

  obtain ⟨n, hn⟩ : ∃ n : ℕ, b ≤ (n : ℝ) := ⟨Nat.ceil b, Nat.le_ceil b⟩

  obtain ⟨M, hMpos, hM⟩ :=
    gamma_real_interval_bound (a := 1 - b + n) (b := 1 - a + n) (by linarith)

  have hcont : Continuous fun p : ℝ × ℝ =>
      ‖(Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))⁻¹‖ := by
    apply Continuous.norm
    exact Complex.differentiable_one_div_Gamma.continuous.comp (by continuity)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := a) (b := b)).prod (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
      |>.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max (M / Real.pi) (max C 1), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (le_max_right _ _))
  · intro s hs
    obtain ⟨hsa, hsb⟩ := hs
    rcases le_or_gt (1 : ℝ) |s.im| with hbig | hsmall
    ·
      have him : s.im ≠ 0 := by
        intro h0; rw [h0, abs_zero] at hbig; norm_num at hbig
      have him1 : 1 ≤ |(1 - s).im| := by
        have : (1 - s).im = -s.im := by simp
        rw [this, abs_neg]; exact hbig
      have hre : (1 - s + (n : ℂ)).re = 1 - s.re + (n : ℝ) := by simp
      have hpos : 0 < (1 - s + (n : ℂ)).re := by
        rw [hre]; linarith
      have hmem : (1 - s + (n : ℂ)).re ∈ Set.Icc (1 - b + n) (1 - a + n) := by
        rw [hre, Set.mem_Icc]; constructor <;> linarith
      have hGbound : ‖Complex.Gamma (1 - s)‖ ≤ M := by
        calc ‖Complex.Gamma (1 - s)‖ ≤ ‖Complex.Gamma (1 - s + (n : ℂ))‖ :=
              gamma_norm_le_add_nat him1 n
          _ ≤ Real.Gamma ((1 - s + (n : ℂ)).re) := gamma_norm_le_real hpos
          _ ≤ M := hM _ hmem
      have hSbound : ‖Complex.sin ((Real.pi : ℂ) * s)‖ ≤ Real.exp (Real.pi * |s.im|) := by
        have h := complex_sin_norm_le_exp_im ((Real.pi : ℂ) * s)
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          abs_mul, abs_of_pos Real.pi_pos] at h
        exact h
      rw [gamma_inv_reflection him, norm_div, norm_mul]
      have hnorm : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [abs_of_pos Real.pi_pos]
      rw [hnorm]
      calc ‖Complex.Gamma (1 - s)‖ * ‖Complex.sin ((Real.pi : ℂ) * s)‖ / Real.pi
          ≤ M * Real.exp (Real.pi * |s.im|) / Real.pi := by
            apply div_le_div_of_nonneg_right _ Real.pi_pos.le
            exact mul_le_mul hGbound hSbound (norm_nonneg _) hMpos.le
        _ = M / Real.pi * Real.exp (Real.pi * |s.im|) := by ring
        _ ≤ max (M / Real.pi) (max C 1) * Real.exp (Real.pi * |s.im|) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    ·
      have hGpos : 0 < max (M / Real.pi) (max C 1) :=
        lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (le_max_right _ _))
      have hmemK : (s.re, s.im) ∈ Set.Icc a b ×ˢ Set.Icc (-1 : ℝ) 1 :=
        ⟨⟨hsa, hsb⟩,
          ⟨by linarith [neg_abs_le s.im, hsmall], by linarith [le_abs_self s.im, hsmall]⟩⟩
      have hCapp := hC (s.re, s.im) hmemK
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Complex.re_add_im] at hCapp
      calc ‖(Complex.Gamma s)⁻¹‖ ≤ C := hCapp
        _ ≤ max (M / Real.pi) (max C 1) := le_trans (le_max_left C 1) (le_max_right _ _)
        _ = max (M / Real.pi) (max C 1) * 1 := (mul_one _).symm
        _ ≤ max (M / Real.pi) (max C 1) * Real.exp (Real.pi * |s.im|) :=
            mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity)) hGpos.le

theorem gammaC_inverse_strip_exp_bound (a b : ℝ) (hab : a ≤ b) :
    ∃ GC : ℝ, 0 < GC ∧ ∀ s : ℂ, a ≤ s.re ∧ s.re ≤ b →
      ‖(Complex.Gammaℂ s)⁻¹‖ ≤ GC * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨G, hGpos, hG⟩ := gamma_inverse_strip_exp_bound a b hab
  refine ⟨max (G * (2 * Real.pi) ^ b / 2) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · intro s hs
    obtain ⟨hsa, hsb⟩ := hs
    have hbase : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring

    have hpow : ‖(2 * (2 * (Real.pi : ℂ)) ^ (-s))⁻¹‖ = (2 * Real.pi) ^ s.re / 2 := by
      rw [norm_inv, norm_mul, hbase, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
        Complex.neg_re, Complex.norm_ofNat, Real.rpow_neg (by positivity)]
      field_simp
    have hle : (2 * Real.pi) ^ s.re ≤ (2 * Real.pi) ^ b :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hsb
    have hGs : ‖(Complex.Gamma s)⁻¹‖ ≤ G * Real.exp (Real.pi * |s.im|) := hG s ⟨hsa, hsb⟩
    rw [Complex.Gammaℂ_def]
    have hnorm : ‖(2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s)⁻¹‖ =
        ‖(2 * (2 * (Real.pi : ℂ)) ^ (-s))⁻¹‖ * ‖(Complex.Gamma s)⁻¹‖ := by
      rw [mul_inv, norm_mul]
    rw [hnorm]
    calc ‖(2 * (2 * (Real.pi : ℂ)) ^ (-s))⁻¹‖ * ‖(Complex.Gamma s)⁻¹‖
        ≤ ((2 * Real.pi) ^ s.re / 2) * (G * Real.exp (Real.pi * |s.im|)) := by
          refine mul_le_mul hpow.le hGs (norm_nonneg _) ?_
          positivity
      _ ≤ ((2 * Real.pi) ^ b / 2) * (G * Real.exp (Real.pi * |s.im|)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hGpos.le (Real.exp_pos _).le)
          exact div_le_div_of_nonneg_right hle (by norm_num)
      _ = G * (2 * Real.pi) ^ b / 2 * Real.exp (Real.pi * |s.im|) := by ring
      _ ≤ max (G * (2 * Real.pi) ^ b / 2) 1 * Real.exp (Real.pi * |s.im|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end DedekindZetaZeroFree
