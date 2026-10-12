module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.OriginContourShift

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve

theorem fieldTransform_origin_remainder_uniform_bound
    (D : ℝ) (r : ℕ) (b δ : ℝ) (j : ℕ)
    (hD : 0 < D) (hr : 1 ≤ r) (hb : 0 < b)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
        (∀ x : ℝ, b < x → h x = 0) →
        ∀ x : ℝ, 0 < x → x ≤ 1 →
          ‖Vendor.EulerIter j (fun y : ℝ => fieldTransform D r h y -
            Polynomial.eval (Real.log y : ℂ) (originPolynomial D r h)) x‖ ≤
              C * Vendor.S b N h * x ^ δ := by
  obtain ⟨N, C, hC, hbound⟩ :=
    B_negative_line_uniform_integral_bound D r b δ j hD hr hb hδ hδ1
  refine ⟨N, (1 / (2 * Real.pi)) * C, by positivity, ?_⟩
  intro h hh hhc hsupp x hx _
  rw [EulerIter_fieldTransform_sub_originPolynomial_eq_mellinInv
    D r h hD hr hh hhc j δ x hδ hδ1 hx]
  obtain ⟨_, hInt⟩ := hbound h hh hhc hsupp
  have hInt' : (∫ t : ℝ, ‖(-((↑(-δ)) + (t : ℂ) * Complex.I)) ^ j *
      B D r h ((↑(-δ)) + (t : ℂ) * Complex.I)‖) ≤ C * Vendor.S b N h := by
    simpa only [Complex.ofReal_neg] using hInt
  have hpi : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
  have hnorm : ∀ t : ℝ, ‖(x : ℂ) ^ (-((↑(-δ)) + (t : ℂ) * Complex.I)) •
      ((-((↑(-δ)) + (t : ℂ) * Complex.I)) ^ j *
        B D r h ((↑(-δ)) + (t : ℂ) * Complex.I))‖
      = x ^ δ * ‖(-((↑(-δ)) + (t : ℂ) * Complex.I)) ^ j *
        B D r h ((↑(-δ)) + (t : ℂ) * Complex.I)‖ := by
    intro t
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    congr 1
    simp [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.I_re, Complex.I_im]
  have hIntEq : (∫ t : ℝ, ‖(x : ℂ) ^ (-((↑(-δ)) + (t : ℂ) * Complex.I)) •
      ((-((↑(-δ)) + (t : ℂ) * Complex.I)) ^ j *
        B D r h ((↑(-δ)) + (t : ℂ) * Complex.I))‖)
      = x ^ δ * ∫ t : ℝ, ‖(-((↑(-δ)) + (t : ℂ) * Complex.I)) ^ j *
          B D r h ((↑(-δ)) + (t : ℂ) * Complex.I)‖ := by
    simp_rw [hnorm]
    rw [integral_const_mul]
  have hstep : ‖mellinInv (-δ) (fun s : ℂ => (-s) ^ j * B D r h s) x‖ ≤
      (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖(x : ℂ) ^ (-((↑(-δ)) + (t : ℂ) * Complex.I)) •
        ((-((↑(-δ)) + (t : ℂ) * Complex.I)) ^ j *
          B D r h ((↑(-δ)) + (t : ℂ) * Complex.I))‖ := by
    rw [mellinInv]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpi]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hpi.le
  calc ‖mellinInv (-δ) (fun s : ℂ => (-s) ^ j * B D r h s) x‖
      ≤ (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖(x : ℂ) ^ (-((↑(-δ)) + (t : ℂ) * Complex.I)) •
        ((-((↑(-δ)) + (t : ℂ) * Complex.I)) ^ j *
          B D r h ((↑(-δ)) + (t : ℂ) * Complex.I))‖ := hstep
    _ = (1 / (2 * Real.pi)) * (x ^ δ * ∫ t : ℝ, ‖(-((↑(-δ)) + (t : ℂ) * Complex.I)) ^ j *
          B D r h ((↑(-δ)) + (t : ℂ) * Complex.I)‖) := by rw [hIntEq]
    _ ≤ (1 / (2 * Real.pi)) * (x ^ δ * (C * Vendor.S b N h)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hInt' (Real.rpow_nonneg hx.le δ)) hpi.le
    _ = ((1 / (2 * Real.pi)) * C) * Vendor.S b N h * x ^ δ := by ring

theorem originPolynomial_coeff_uniform_bound
    (D : ℝ) (r : ℕ) (b : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hb : 0 < b) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
        (∀ x : ℝ, b < x → h x = 0) →
        ∀ n : ℕ, n < r →
          ‖(originPolynomial D r h).coeff n‖ ≤ C * Vendor.S b N h := by
  obtain ⟨N, C, hC, hA⟩ := A_uniform_disk_bound D r b hD hr hb
  refine ⟨N, 2 ^ (r - 1) * C, by positivity, ?_⟩
  intro h hh hhc hsupp n hn
  have hS : 0 ≤ Vendor.S b N h := Vendor.S_nonneg b hb N h hh
  have hM : 0 ≤ C * Vendor.S b N h := mul_nonneg hC.le hS
  have hdisk : Metric.closedBall (0 : ℂ) (1 / 2 : ℝ) ⊆ {s : ℂ | -1 < s.re} := by
    intro s hs
    simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_setOf_eq] at hs ⊢
    have := Complex.abs_re_le_norm s
    rw [abs_le] at this
    linarith [this.1]
  have hbound : ∀ s ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ),
      ‖A D r h s‖ ≤ C * Vendor.S b N h :=
    fun s hs => hA h hh hhc hsupp s (by
      simpa [Metric.mem_closedBall, dist_zero_right] using hs)
  have hres := Vendor.originLogResiduePolynomial_coeff_norm_le {s : ℂ | -1 < s.re}
    (isOpen_lt continuous_const Complex.continuous_re) (by simp) (A D r h)
    (A_analyticOnNhd D r h hD hr hh hhc) r n hr hn (C * Vendor.S b N h) hM hdisk hbound
  have hfac : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
  have h2 : (2 : ℝ) ^ (r - n - 1) ≤ (2 : ℝ) ^ (r - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc ‖(originPolynomial D r h).coeff n‖
      = ‖(Vendor.originLogResiduePolynomial (A D r h) r).coeff n‖ := rfl
    _ ≤ 2 ^ (r - n - 1) * (C * Vendor.S b N h) / (n.factorial : ℝ) := hres
    _ ≤ 2 ^ (r - n - 1) * (C * Vendor.S b N h) :=
        div_le_self (by positivity) hfac
    _ ≤ (2 : ℝ) ^ (r - 1) * (C * Vendor.S b N h) :=
        mul_le_mul_of_nonneg_right h2 hM
    _ = (2 ^ (r - 1) * C) * Vendor.S b N h := by ring

end DedekindZetaZeroFree.LargeSieve

end
