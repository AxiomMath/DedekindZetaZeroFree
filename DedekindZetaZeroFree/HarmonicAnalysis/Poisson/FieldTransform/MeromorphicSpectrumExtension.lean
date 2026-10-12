module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.SpectralMultiplier

@[expose] public section

noncomputable section
open scoped Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve

def A (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  (D : ℂ) ^ (s - 1 / 2) *
    (((2 * Real.pi : ℝ) : ℂ) * Complex.Gammaℂ (s + 1)) ^ r *
    ((Complex.Gammaℂ (1 - s))⁻¹) ^ (r - 1) * Vendor.originMellinQ h (1 - s)

private lemma differentiableAt_Gammaℂ {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) :
    DifferentiableAt ℂ Complex.Gammaℂ s := by
  have hfun : Complex.Gammaℂ =
      fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-z) * Complex.Gamma z := by
    funext z; rw [Complex.Gammaℂ_def]
  rw [hfun]
  have hbase : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  refine DifferentiableAt.mul ?_ (Complex.differentiableAt_Gamma s hs)
  exact (differentiableAt_const _).mul ((differentiableAt_id.neg).const_cpow (Or.inl hbase))

private lemma Gammaℂ_mul_add_one {s : ℂ} (hs : s ≠ 0) :
    ((2 * Real.pi : ℝ) : ℂ) * Complex.Gammaℂ (s + 1) = Complex.Gammaℂ s * s := by
  rw [Complex.Gammaℂ_add_one hs, div_eq_mul_inv, div_eq_mul_inv]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

private lemma differentiableAt_A (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (hD : 0 < D)
    (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ (A D r h) s := by
  have hDne : (D : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hD
  have hs1 : ∀ m : ℕ, s + 1 ≠ -m := by
    intro m hc
    have h1 : (s + 1).re = -(m : ℝ) := by rw [hc]; simp
    have h2 : (s + 1).re = s.re + 1 := by simp
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hDcp : DifferentiableAt ℂ (fun z : ℂ => (D : ℂ) ^ (z - 1 / 2)) s :=
    ((differentiableAt_id.sub_const (1 / 2 : ℂ))).const_cpow (Or.inl hDne)
  have hG : DifferentiableAt ℂ
      (fun z : ℂ => (((2 * Real.pi : ℝ) : ℂ) * Complex.Gammaℂ (z + 1)) ^ r) s :=
    (((differentiableAt_const (((2 * Real.pi : ℝ) : ℂ))).mul
      ((differentiableAt_Gammaℂ hs1).comp s (differentiableAt_id.add_const 1)))).pow r
  have hG2 : DifferentiableAt ℂ (fun z : ℂ => ((Complex.Gammaℂ (1 - z))⁻¹) ^ (r - 1)) s :=
    ((Complex.differentiable_Gammaℂ_inv.differentiableAt.comp s
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id))).pow (r - 1)
  have hQ : DifferentiableAt ℂ (fun z : ℂ => Vendor.originMellinQ h (1 - z)) s :=
    (Vendor.originMellinQ_differentiable h hh hhc).differentiableAt.comp s
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)
  exact (((hDcp.mul hG).mul hG2).mul hQ)

theorem A_analyticOnNhd (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) :
    AnalyticOnNhd ℂ (A D r h) {s : ℂ | -1 < s.re} :=
  DifferentiableOn.analyticOnNhd
    (fun s hs => (differentiableAt_A D r h hD hh hhc hs).differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)

theorem B_eq_A_div (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (s : ℂ) (hs : -1 < s.re) (hs0 : s ≠ 0) :
    B D r h s = A D r h s / s ^ r := by
  have hpow : (((2 * Real.pi : ℝ) : ℂ) * Complex.Gammaℂ (s + 1)) ^ r =
      Complex.Gammaℂ s ^ r * s ^ r := by
    rw [Gammaℂ_mul_add_one hs0, mul_pow]
  simp only [B, A, hpow]
  field_simp

theorem A_div_analyticOnNhd (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) :
    AnalyticOnNhd ℂ (fun s : ℂ => A D r h s / s ^ r)
      {s : ℂ | -1 < s.re ∧ s ≠ 0} := by
  refine AnalyticOnNhd.div ?_ ?_ ?_
  · exact (A_analyticOnNhd D r h hD hr hh hhc).mono (fun s hs => hs.1)
  · exact (analyticOnNhd_id (𝕜 := ℂ) (s := {s : ℂ | -1 < s.re ∧ s ≠ 0})).pow r
  · intro x hx; exact pow_ne_zero r hx.2

private lemma A_zero_aux (D : ℝ) (r : ℕ) (hr : 1 ≤ r) (m : ℂ) :
    (D : ℂ) ^ (-(1 / 2 : ℂ)) * (((2 * Real.pi : ℝ) : ℂ) * Complex.Gammaℂ 1) ^ r *
      ((Complex.Gammaℂ 1)⁻¹) ^ (r - 1) * (m / Complex.Gammaℂ 1) =
    (D : ℂ) ^ (-(1 / 2 : ℂ)) * (((2 * Real.pi : ℝ) : ℂ) ^ r) * m := by
  rw [Complex.Gammaℂ_one]
  have h2 : ((2 * Real.pi : ℝ) : ℂ) * (1 / (Real.pi : ℂ)) = 2 := by
    push_cast
    field_simp
  have h3 : (1 / (Real.pi : ℂ))⁻¹ = (Real.pi : ℂ) := by
    rw [one_div, inv_inv]
  have h4 : m / (1 / (Real.pi : ℂ)) = m * (Real.pi : ℂ) := by
    rw [one_div, div_eq_mul_inv, inv_inv]
  rw [h2, h3, h4]
  have hpow : (2 : ℂ) ^ r * (Real.pi : ℂ) ^ (r - 1) * (Real.pi : ℂ) =
      (((2 * Real.pi : ℝ) : ℂ)) ^ r := by
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hr, ← mul_pow]
    push_cast
    ring
  rw [← hpow]
  ring

theorem A_zero (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) :
    A D r h 0 = (D : ℂ) ^ (-(1 / 2 : ℂ)) *
      (((2 * Real.pi : ℝ) : ℂ) ^ r) * mellin h 1 := by
  have hQ1 : Vendor.originMellinQ h 1 = mellin h 1 / Complex.Gammaℂ 1 :=
    Vendor.originMellinQ_eq_mellin_div_Gammaℂ h hh hhc 1 (by norm_num)
  simp only [A, zero_sub, zero_add, sub_zero, hQ1]
  exact A_zero_aux D r hr (mellin h 1)

theorem A_uniform_disk_bound (D : ℝ) (r : ℕ) (b : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hb : 0 < b) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
        (∀ x : ℝ, b < x → h x = 0) →
        ∀ s : ℂ, ‖s‖ ≤ (1 / 2 : ℝ) → ‖A D r h s‖ ≤ C * Vendor.S b N h := by
  have hDne : (D : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hD
  set K : Set ℂ := Metric.closedBall (0 : ℂ) (1 / 2 : ℝ) with hKdef
  have hK : IsCompact K := isCompact_closedBall (0 : ℂ) (1 / 2 : ℝ)
  set K' : Set ℂ := (fun s : ℂ => 1 - s) '' K with hK'def
  have hK' : IsCompact K' := hK.image (continuous_const.sub continuous_id)
  obtain ⟨N, C', hC'pos, hbound⟩ := Vendor.originMellinQ_compact_source_bound b hb K' hK'
  have hs1 : ∀ s ∈ K, ∀ m : ℕ, s + 1 ≠ -m := by
    intro s hsK m hc
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hre : (s + 1).re = -(m : ℝ) := by rw [hc]; simp
    have hre2 : (s + 1).re = s.re + 1 := by simp
    have hle : ‖s‖ ≤ (1 / 2 : ℝ) := by
      rw [hKdef, Metric.mem_closedBall] at hsK; simpa using hsK
    have habs : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
    rw [hre2] at hre
    linarith [neg_le_abs s.re]
  have hc1 : ContinuousOn (fun s : ℂ => (D : ℂ) ^ (s - 1 / 2)) K :=
    ((differentiable_id.sub_const (1 / 2 : ℂ)).const_cpow (Or.inl hDne)).continuous.continuousOn
  have hdG : DifferentiableOn ℂ (fun s : ℂ => Complex.Gammaℂ (s + 1)) K := fun s hsK =>
    ((differentiableAt_Gammaℂ (hs1 s hsK)).comp s (differentiableAt_id.add_const 1)).differentiableWithinAt
  have hcG : ContinuousOn (fun s : ℂ => Complex.Gammaℂ (s + 1)) K := hdG.continuousOn
  have hc2 : ContinuousOn (fun s : ℂ => (((2 * Real.pi : ℝ) : ℂ) * Complex.Gammaℂ (s + 1)) ^ r) K :=
    (continuousOn_const.mul hcG).pow r
  have hcInv : ContinuousOn (fun s : ℂ => (Complex.Gammaℂ (1 - s))⁻¹) K :=
    Complex.differentiable_Gammaℂ_inv.continuous.comp_continuousOn
      ((continuous_const.sub continuous_id).continuousOn)
  have hc3 : ContinuousOn (fun s : ℂ => ((Complex.Gammaℂ (1 - s))⁻¹) ^ (r - 1)) K :=
    hcInv.pow (r - 1)
  obtain ⟨M1, hM1⟩ := hK.exists_bound_of_continuousOn hc1
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn hc2
  obtain ⟨M3, hM3⟩ := hK.exists_bound_of_continuousOn hc3
  refine ⟨N, max M1 1 * max M2 1 * max M3 1 * C', ?_, ?_⟩
  · exact mul_pos (mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _))) hC'pos
  · intro h hhd hhc hsupp s hsK'
    have hsK : s ∈ K := by
      rw [hKdef, Metric.mem_closedBall] at *; simpa using hsK'
    have b1 : ‖(D : ℂ) ^ (s - 1 / 2)‖ ≤ max M1 1 := (hM1 s hsK).trans (le_max_left _ _)
    have b2 : ‖(((2 * Real.pi : ℝ) : ℂ) * Complex.Gammaℂ (s + 1)) ^ r‖ ≤ max M2 1 :=
      (hM2 s hsK).trans (le_max_left _ _)
    have b3 : ‖((Complex.Gammaℂ (1 - s))⁻¹) ^ (r - 1)‖ ≤ max M3 1 :=
      (hM3 s hsK).trans (le_max_left _ _)
    have bQ : ‖Vendor.originMellinQ h (1 - s)‖ ≤ C' * Vendor.S b N h :=
      hbound h hhd hhc (fun x hx => hsupp x hx) (1 - s) ⟨s, hsK, rfl⟩
    simp only [A]
    calc ‖(D : ℂ) ^ (s - 1 / 2) * (((2 * Real.pi : ℝ) : ℂ) * Complex.Gammaℂ (s + 1)) ^ r *
            ((Complex.Gammaℂ (1 - s))⁻¹) ^ (r - 1) * Vendor.originMellinQ h (1 - s)‖
        ≤ ‖(D : ℂ) ^ (s - 1 / 2)‖ * ‖(((2 * Real.pi : ℝ) : ℂ) * Complex.Gammaℂ (s + 1)) ^ r‖ *
            ‖((Complex.Gammaℂ (1 - s))⁻¹) ^ (r - 1)‖ * ‖Vendor.originMellinQ h (1 - s)‖ := by
          rw [norm_mul, norm_mul, norm_mul]
      _ ≤ max M1 1 * max M2 1 * max M3 1 * (C' * Vendor.S b N h) := by
          gcongr
      _ = (max M1 1 * max M2 1 * max M3 1 * C') * Vendor.S b N h := by ring

end DedekindZetaZeroFree.LargeSieve

end
