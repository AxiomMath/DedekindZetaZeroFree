module

public import DedekindZetaZeroFree.Analysis.CompactSupport.IteratedDerivatives

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped NumberField Classical ContDiff Topology

namespace DedekindZetaZeroFree.LargeSieve.Vendor

private lemma contDiff_iteratedDeriv_of_smooth {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n h) := by
  rw [iteratedDeriv_eq_iterate]
  exact hh.iterate_deriv n

private lemma hasCompactSupport_iteratedDeriv_of_compact {h : ℝ → ℂ} (hh : HasCompactSupport h)
    (n : ℕ) : HasCompactSupport (iteratedDeriv n h) := by
  rw [iteratedDeriv_eq_iterate]
  induction n with
  | zero => simpa using hh
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.deriv

private lemma eventually_eq_zero_atTop_of_hasCompactSupport {f : ℝ → ℂ}
    (hf : HasCompactSupport f) : ∀ᶠ t : ℝ in atTop, f t = 0 := by
  obtain ⟨K, hKc, hK0⟩ := exists_compact_iff_hasCompactSupport.mpr hf
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn continuousOn_id
  refine eventually_atTop.2 ⟨R + 1, fun t ht => hK0 t fun htK => ?_⟩
  have h1 : ‖t‖ ≤ R := by simpa using hR t htK
  rw [Real.norm_eq_abs, abs_le] at h1
  linarith [h1.2]

private lemma isBigO_exp_atTop_of_hasCompactSupport {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    f =O[atTop] (fun t : ℝ => Real.exp (-1 * t)) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [eventually_eq_zero_atTop_of_hasCompactSupport hf] with t ht
  simp [ht]

private lemma isBigO_rpow_zero_atZero {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) : f =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (0 : ℝ)) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf
  refine IsBigO.of_bound (max C 1) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Real.rpow_zero, norm_one, mul_one]
  exact (hC t).trans (le_max_left _ _)

private lemma isBigO_rpow_zero_atZero' {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) : f =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  simpa only [neg_zero] using isBigO_rpow_zero_atZero hf hc

private lemma integral_Ioc_rpow' (R : ℝ) (hR : 0 < R) (r : ℝ) (hr : 0 < r) :
    ∫ t in Ioc (0 : ℝ) R, t ^ (r - 1) = R ^ r / r := by
  rw [← intervalIntegral.integral_of_le hR.le]
  rw [integral_rpow (Or.inl (by linarith : -1 < r - 1))]
  rw [Real.zero_rpow (by linarith : r - 1 + 1 ≠ 0), sub_zero, sub_add_cancel]

private lemma integral_indicator_rpow_bound (M R a b : ℝ) (hM : 0 ≤ M) (hR : 0 < R)
    (ha : 0 < a) (hb : 0 < b) :
    ∫ t, (Ioc (0 : ℝ) R).indicator (fun t : ℝ => M * (t ^ (a - 1) + t ^ (b - 1))) t
        ∂(volume.restrict (Ioi 0)) = M * (R ^ a / a + R ^ b / b) := by
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
  rw [integral_const_mul]
  congr 1
  rw [integral_add]
  · rw [integral_Ioc_rpow' R hR a ha, integral_Ioc_rpow' R hR b hb]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < a - 1))
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < b - 1))

theorem mellinConvergent_iteratedDeriv_of_pos {h : ℝ → ℂ}
    (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (iteratedDeriv n h) s := by
  have hfcont : Continuous (iteratedDeriv n h) := (contDiff_iteratedDeriv_of_smooth hh n).continuous
  have hfcomp : HasCompactSupport (iteratedDeriv n h) := hasCompactSupport_iteratedDeriv_of_compact hcompact n
  exact mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := 0) one_pos
    (hfcont.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (isBigO_exp_atTop_of_hasCompactSupport hfcomp)
    (isBigO_rpow_zero_atZero' hfcont hfcomp) hs

theorem differentiableAt_mellin_iteratedDeriv_of_pos {h : ℝ → ℂ}
    (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (iteratedDeriv n h)) s := by
  have hfcont : Continuous (iteratedDeriv n h) := (contDiff_iteratedDeriv_of_smooth hh n).continuous
  have hfcomp : HasCompactSupport (iteratedDeriv n h) := hasCompactSupport_iteratedDeriv_of_compact hcompact n
  exact mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) (b := 0) one_pos
    (hfcont.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (isBigO_exp_atTop_of_hasCompactSupport hfcomp)
    (isBigO_rpow_zero_atZero' hfcont hfcomp) hs

theorem mellin_iteratedDeriv_positive_strip_bound {h : ℝ → ℂ}
    (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    (n : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖mellin (iteratedDeriv n h) s‖ ≤ C := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hfcont : Continuous (iteratedDeriv n h) := (contDiff_iteratedDeriv_of_smooth hh n).continuous
  have hfcomp : HasCompactSupport (iteratedDeriv n h) := hasCompactSupport_iteratedDeriv_of_compact hcompact n
  obtain ⟨C₀, hC₀⟩ := hfcomp.exists_bound_of_continuous hfcont
  set M : ℝ := max C₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ t : ℝ, ‖iteratedDeriv n h t‖ ≤ M := fun t => (hC₀ t).trans (le_max_left _ _)
  obtain ⟨K, hKc, hK0⟩ := exists_compact_iff_hasCompactSupport.mpr hfcomp
  obtain ⟨R₀, hR₀⟩ := hKc.exists_bound_of_continuousOn continuousOn_id
  set R : ℝ := max R₀ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsupp : ∀ t : ℝ, iteratedDeriv n h t ≠ 0 → t ≤ R := by
    intro t ht
    have htK : t ∈ K := by
      by_contra hcon
      exact ht (hK0 t hcon)
    have h1 : ‖t‖ ≤ R₀ := by simpa using hR₀ t htK
    rw [Real.norm_eq_abs, abs_le] at h1
    linarith [h1.2, le_max_left R₀ 1]
  refine ⟨M * (R ^ a / a + R ^ b / b) + 1, ?_, ?_⟩
  · have h1 : 0 ≤ M * (R ^ a / a + R ^ b / b) :=
      mul_nonneg hM0 (add_nonneg (div_nonneg (Real.rpow_nonneg hRpos.le a) ha.le)
        (div_nonneg (Real.rpow_nonneg hRpos.le b) hb.le))
    linarith
  · intro s hs1 hs2
    have hpt : ∀ t : ℝ, 0 < t →
        ‖(t : ℂ) ^ (s - 1) • iteratedDeriv n h t‖ ≤
          (Ioc (0 : ℝ) R).indicator (fun t : ℝ => M * (t ^ (a - 1) + t ^ (b - 1))) t := by
      intro t ht0
      by_cases hft : iteratedDeriv n h t = 0
      · rw [hft, smul_zero, norm_zero]
        by_cases hmem : t ∈ Ioc (0 : ℝ) R
        · rw [Set.indicator_of_mem hmem]
          exact mul_nonneg hM0
            (add_nonneg (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg ht0.le _))
        · rw [Set.indicator_of_notMem hmem]
      · have htR : t ≤ R := hsupp t hft
        rw [Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) R from ⟨ht0, htR⟩), norm_smul,
          Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
        have hcmp : t ^ (s.re - 1) ≤ t ^ (a - 1) + t ^ (b - 1) := by
          rcases le_or_gt t 1 with hle | hlt
          · have h := Real.rpow_le_rpow_of_exponent_ge ht0 hle (by linarith : a - 1 ≤ s.re - 1)
            linarith [Real.rpow_nonneg ht0.le (b - 1)]
          · have h := Real.rpow_le_rpow_of_exponent_le hlt.le (by linarith : s.re - 1 ≤ b - 1)
            linarith [Real.rpow_nonneg ht0.le (a - 1)]
        calc t ^ (s.re - 1) * ‖iteratedDeriv n h t‖
            ≤ t ^ (s.re - 1) * M :=
              mul_le_mul_of_nonneg_left (hM t) (Real.rpow_nonneg ht0.le _)
          _ ≤ (t ^ (a - 1) + t ^ (b - 1)) * M := mul_le_mul_of_nonneg_right hcmp hM0
          _ = M * (t ^ (a - 1) + t ^ (b - 1)) := by ring
    have hgint : IntegrableOn (fun t : ℝ => M * (t ^ (a - 1) + t ^ (b - 1)))
        (Ioc (0 : ℝ) R) volume := by
      have h1 : IntegrableOn (fun t : ℝ => t ^ (a - 1)) (Ioc (0 : ℝ) R) volume :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hRpos.le).mp
          (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < a - 1))
      have h2 : IntegrableOn (fun t : ℝ => t ^ (b - 1)) (Ioc (0 : ℝ) R) volume :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hRpos.le).mp
          (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < b - 1))
      exact (h1.add h2).const_mul M
    have hg : Integrable ((Ioc (0 : ℝ) R).indicator
        (fun t : ℝ => M * (t ^ (a - 1) + t ^ (b - 1)))) (volume.restrict (Ioi 0)) :=
      (integrable_indicator_iff measurableSet_Ioc).mpr
        (by simpa only [IntegrableOn, Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
              using hgint)
    have hae : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi 0)),
        ‖(t : ℂ) ^ (s - 1) • iteratedDeriv n h t‖ ≤
          (Ioc (0 : ℝ) R).indicator (fun t : ℝ => M * (t ^ (a - 1) + t ^ (b - 1))) t :=
      (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => hpt t ht)
    have hmain : ‖mellin (iteratedDeriv n h) s‖ ≤ M * (R ^ a / a + R ^ b / b) := by
      have h1 : ‖mellin (iteratedDeriv n h) s‖
          = ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • iteratedDeriv n h t‖ := by
        rw [mellin]
      rw [h1]
      calc ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • iteratedDeriv n h t‖
          ≤ ∫ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) R).indicator
              (fun t : ℝ => M * (t ^ (a - 1) + t ^ (b - 1))) t :=
            MeasureTheory.norm_integral_le_of_norm_le hg hae
        _ = M * (R ^ a / a + R ^ b / b) :=
            integral_indicator_rpow_bound M R a b hM0 hRpos ha hb
    linarith

end DedekindZetaZeroFree.LargeSieve.Vendor

end
