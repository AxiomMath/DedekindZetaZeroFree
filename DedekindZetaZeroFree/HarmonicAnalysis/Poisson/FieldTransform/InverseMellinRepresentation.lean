module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.SpectralMultiplier
public import DedekindZetaZeroFree.Analysis.ContourIntegration.ExponentialStripGrowth

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve

def fieldTransform (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then mellinInv 2 (B D r h) x else 0

private lemma rpow_neg_le_max (c x σ : ℝ) (hx : 0 < x)
    (h : (c ≤ σ ∧ σ ≤ 2) ∨ (2 ≤ σ ∧ σ ≤ c)) :
    x ^ (-σ) ≤ max (x ^ (-c)) (x ^ (-2 : ℝ)) := by
  rcases le_total 1 x with hx1 | hx1
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)).trans (le_max_right _ _)
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)).trans (le_max_left _ _)

theorem B_inverse_integrable (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    MeasureTheory.Integrable (fun t : ℝ =>
      (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)) *
        B D r h ((c : ℂ) + (t : ℂ) * Complex.I)) MeasureTheory.volume := by
  obtain ⟨C, hCpos, hC⟩ := B_rapid_bound D r h c c 2 hD hr hh hhc hc le_rfl
  have hcont : Continuous (fun t : ℝ => B D r h ((c : ℂ) + (t : ℂ) * Complex.I)) :=
    (B_differentiableOn D r h hD hr hh hhc).continuousOn.comp_continuous (by fun_prop)
      (fun t => by
        simp only [Set.mem_setOf_eq, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
        simpa using hc)
  haveI : NeZero ((x : ℂ)) := ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
  have hcpow : Continuous (fun t : ℝ => (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))) :=
    (differentiable_const_cpow_of_neZero (x : ℂ)).continuous.comp (by fun_prop)
  refine Integrable.mono' (g := fun t : ℝ => (x ^ (-c) * C) * (1 + |t|) ^ (-2 : ℝ))
    ?_ (hcpow.mul hcont).aestronglyMeasurable ?_
  · have h1 : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-2 : ℝ)) volume :=
      integrable_one_add_norm (E := ℝ) (r := 2) (by rw [Module.finrank_self]; norm_num)
    have h2 : Integrable (fun t : ℝ => (1 + |t|) ^ (-2 : ℝ)) volume := by
      simpa [Real.norm_eq_abs] using h1
    exact h2.const_mul _
  · refine Eventually.of_forall fun t => ?_
    have h1 : ‖(x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))‖ = x ^ (-c) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
    have h2 : ‖B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1 + |t|) ^ 2 := by
      have hp : (0 : ℝ) < (1 + |t|) ^ 2 := by positivity
      rw [le_div_iff₀ hp, mul_comm]
      exact hC c (by simp) t
    calc ‖(x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)) *
            B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖
        = ‖(x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))‖ *
            ‖B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖ := norm_mul _ _
      _ = x ^ (-c) * ‖B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖ := by rw [h1]
      _ ≤ x ^ (-c) * (C / (1 + |t|) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx.le _)
      _ = (x ^ (-c) * C) * (1 + |t|) ^ (-2 : ℝ) := by
          rw [Real.rpow_neg (show (0 : ℝ) ≤ 1 + |t| by positivity), Real.rpow_two,
            div_eq_mul_inv]
          ring

theorem B_mellinInv_eq (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    mellinInv c (B D r h) x = mellinInv 2 (B D r h) x := by
  rw [Vendor.mellinInv_eq_verticalIntegral c (B D r h) hx,
    Vendor.mellinInv_eq_verticalIntegral 2 (B D r h) hx]
  haveI : NeZero ((x : ℂ)) := ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
  have hcpowd : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ (-s)) :=
    (differentiable_const_cpow_of_neZero (x : ℂ)).comp differentiable_neg
  have hBdiff : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ (B D r h) s := fun s hs =>
    (B_differentiableOn D r h hD hr hh hhc).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  rcases le_total c 2 with hle | hle
  · obtain ⟨C, hCpos, hC⟩ := B_rapid_bound D r h c 2 0 hD hr hh hhc hc hle
    refine Vendor.integral_eq_of_exponential_strip_growth hle
      (fun s => (x : ℂ) ^ (-s) * B D r h s) ?_ ?_ ?_ ?_
    · intro s hs1 hs2
      exact (hcpowd.differentiableAt).mul (hBdiff s (lt_of_lt_of_le hc hs1))
    · exact B_inverse_integrable D r h hD hr hh hhc c x hc hx
    · exact B_inverse_integrable D r h hD hr hh hhc 2 x (by norm_num) hx
    · refine ⟨0, max (x ^ (-c)) (x ^ (-2 : ℝ)) * C, le_refl 0,
        mul_nonneg (le_trans (Real.rpow_nonneg hx.le _) (le_max_left _ _)) hCpos.le,
        fun σ hσ t => ?_⟩
      have hσ' : (c ≤ σ ∧ σ ≤ 2) ∨ (2 ≤ σ ∧ σ ≤ c) := Or.inl ⟨hσ.1, hσ.2⟩
      have h1 : ‖(x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ = x ^ (-σ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
        simp [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
      have h2 : ‖B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
        simpa using hC σ hσ t
      calc ‖(x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
              B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          = ‖(x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ *
              ‖B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_mul _ _
        _ = x ^ (-σ) * ‖B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by rw [h1]
        _ ≤ max (x ^ (-c)) (x ^ (-2 : ℝ)) * C :=
            mul_le_mul (rpow_neg_le_max c x σ hx hσ') h2 (norm_nonneg _)
              (le_trans (Real.rpow_nonneg hx.le _) (le_max_left _ _))
        _ = max (x ^ (-c)) (x ^ (-2 : ℝ)) * C * Real.exp (0 * |t|) := by simp
  · obtain ⟨C, hCpos, hC⟩ := B_rapid_bound D r h 2 c 0 hD hr hh hhc (by norm_num) hle
    refine (Vendor.integral_eq_of_exponential_strip_growth hle
      (fun s => (x : ℂ) ^ (-s) * B D r h s) ?_ ?_ ?_ ?_).symm
    · intro s hs1 hs2
      exact (hcpowd.differentiableAt).mul
        (hBdiff s (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hs1))
    · exact B_inverse_integrable D r h hD hr hh hhc 2 x (by norm_num) hx
    · exact B_inverse_integrable D r h hD hr hh hhc c x hc hx
    · refine ⟨0, max (x ^ (-c)) (x ^ (-2 : ℝ)) * C, le_refl 0,
        mul_nonneg (le_trans (Real.rpow_nonneg hx.le _) (le_max_left _ _)) hCpos.le,
        fun σ hσ t => ?_⟩
      have hσ' : (c ≤ σ ∧ σ ≤ 2) ∨ (2 ≤ σ ∧ σ ≤ c) := Or.inr ⟨hσ.1, hσ.2⟩
      have h1 : ‖(x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ = x ^ (-σ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
        simp [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
      have h2 : ‖B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
        simpa using hC σ hσ t
      calc ‖(x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
              B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          = ‖(x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ *
              ‖B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_mul _ _
        _ = x ^ (-σ) * ‖B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by rw [h1]
        _ ≤ max (x ^ (-c)) (x ^ (-2 : ℝ)) * C :=
            mul_le_mul (rpow_neg_le_max c x σ hx hσ') h2 (norm_nonneg _)
              (le_trans (Real.rpow_nonneg hx.le _) (le_max_left _ _))
        _ = max (x ^ (-c)) (x ^ (-2 : ℝ)) * C * Real.exp (0 * |t|) := by simp

end DedekindZetaZeroFree.LargeSieve

end
