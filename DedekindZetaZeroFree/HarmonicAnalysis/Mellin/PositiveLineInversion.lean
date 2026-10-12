module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.RegularizedVerticalDecay

@[expose] public section

noncomputable section

open MeasureTheory

open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.Vendor

theorem mellin_inversion_positive_line (h : ℝ → ℂ)
    (h_smooth : ContDiff ℝ ∞ h) (h_compact : HasCompactSupport h)
    (σ : ℝ) (hσ : 0 < σ) :
    Complex.VerticalIntegrable (mellin h) σ MeasureTheory.volume ∧
      ∀ x : ℝ, 0 < x → mellinInv σ (mellin h) x = h x := by

  have hF : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ (mellin h) s := by
    intro s hs
    have hd := differentiableAt_mellin_iteratedDeriv_of_pos (h := h) h_smooth h_compact 0 hs
    rwa [iteratedDeriv_zero] at hd
  have hcont : Continuous fun t : ℝ => mellin h ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hF _ (by simp [hσ])).continuousAt.comp (by fun_prop)

  obtain ⟨C, hCpos, hC⟩ :=
    Gammaℂ_mul_originMellinQ_rapid_decay h h_smooth h_compact σ σ le_rfl 2
  have hbound : ∀ t : ℝ, 1 ≤ |t| →
      ‖mellin h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + t ^ 2)⁻¹ := by
    intro t ht
    have hre : 0 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simp [hσ]
    have h1 := hC σ t le_rfl le_rfl ht
    rw [Gammaℂ_mul_originMellinQ_eq_mellin h h_smooth h_compact
      ((σ : ℂ) + (t : ℂ) * Complex.I) hre] at h1
    set d : ℝ := (1 + |t|) ^ 2 with hd
    have hdpos : 0 < d := by positivity
    have h3 : d⁻¹ * (d * ‖mellin h ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ≤ d⁻¹ * C :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hdpos), one_mul] at h3
    have hdt : d⁻¹ ≤ (1 + t ^ 2)⁻¹ := by
      rw [hd]
      exact inv_anti₀ (by positivity) (by nlinarith [abs_nonneg t, sq_abs t])
    calc ‖mellin h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ d⁻¹ * C := h3
      _ = C * d⁻¹ := by ring
      _ ≤ C * (1 + t ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hdt hCpos.le
  have hgi : Integrable (fun t : ℝ => C * (1 + t ^ 2)⁻¹) volume := by
    simpa [smul_eq_mul] using integrable_inv_one_add_sq.const_mul C

  have hIic : IntegrableOn (fun t : ℝ => mellin h ((σ : ℂ) + (t : ℂ) * Complex.I))
      (Set.Iic (-1)) volume := by
    refine Integrable.mono' hgi.integrableOn
      (hcont.stronglyMeasurable.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    exact hbound t (by
      have ht' : t ≤ -1 := ht
      rw [abs_of_nonpos (by linarith)]
      linarith)
  have hIci : IntegrableOn (fun t : ℝ => mellin h ((σ : ℂ) + (t : ℂ) * Complex.I))
      (Set.Ici 1) volume := by
    refine Integrable.mono' hgi.integrableOn
      (hcont.stronglyMeasurable.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact hbound t (le_trans ht (le_abs_self t))

  have hIcc : IntegrableOn (fun t : ℝ => mellin h ((σ : ℂ) + (t : ℂ) * Complex.I))
      (Set.Icc (-1) 1) volume := hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hVI : Complex.VerticalIntegrable (mellin h) σ MeasureTheory.volume := by
    have hIic1 : IntegrableOn (fun t : ℝ => mellin h ((σ : ℂ) + (t : ℂ) * Complex.I))
        (Set.Iic 1) volume := by
      rw [← Set.Iic_union_Icc_eq_Iic (by norm_num : (-1 : ℝ) ≤ 1)]
      exact hIic.union hIcc
    have huniv : IntegrableOn (fun t : ℝ => mellin h ((σ : ℂ) + (t : ℂ) * Complex.I))
        Set.univ volume := by
      rw [← Set.Iic_union_Ici (a := (1 : ℝ))]
      exact hIic1.union hIci
    have : Integrable (fun t : ℝ => mellin h ((σ : ℂ) + (t : ℂ) * Complex.I)) volume := by
      rwa [IntegrableOn, Measure.restrict_univ] at huniv
    exact this
  refine ⟨hVI, fun x hx => ?_⟩
  have hconv : MellinConvergent h σ := by
    have hd := mellinConvergent_iteratedDeriv_of_pos (h := h) h_smooth h_compact 0
      (s := (σ : ℂ)) (by simpa using hσ)
    rwa [iteratedDeriv_zero] at hd
  exact mellinInv_mellin_eq σ h hx hconv hVI (h_smooth.continuous.continuousAt)

end DedekindZetaZeroFree.LargeSieve.Vendor

end
