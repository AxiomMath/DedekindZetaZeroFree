module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LogarithmicContinuation

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace DedekindZetaZeroFree.LargeSieve.Vendor

theorem logMellinContinuation_rapid_vertical_decay {f : ℝ → ℂ} {δ : ℝ}
    {P : Polynomial ℂ} (h : LogMellinPhysical f δ P)
    (u v : ℝ) (hu : -δ < u) (huv : u ≤ v) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, u ≤ σ → σ ≤ v → 1 ≤ |t| →
      (1 + |t|) ^ N *
        ‖logMellinContinuation f P ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  set n : ℕ := max (P.natDegree + 1) (N + 1) with hn
  have hnP : P.natDegree < n := by omega
  have hNn : N ≤ n := by omega
  obtain ⟨C0, hC0, hbound⟩ :=
    LogMellinPhysical.high_euler_uniform_mellin_norm h n hnP u v hu huv
  refine ⟨2 ^ N * C0, by positivity, ?_⟩
  intro σ t hσu hσv ht
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsr : s.re = σ := by rw [hs]; simp
  have hsi : s.im = t := by rw [hs]; simp
  have hs0 : s ≠ 0 := by
    intro hz
    have h1 : s.im = 0 := by rw [hz]; simp
    rw [hsi] at h1
    rw [h1] at ht
    simp only [abs_zero] at ht
    linarith
  have heuler := logMellinContinuation_eq_euler h n hnP s (by rw [hsr]; linarith) hs0
  have hmellin : ‖mellin (EulerIter n f) s‖ ≤ C0 := by
    rw [mellin]
    refine (norm_integral_le_integral_norm _).trans ?_
    simpa only [smul_eq_mul] using (hbound s (by rw [hsr]; exact hσu) (by rw [hsr]; exact hσv)).2
  have hnormz : ‖(-s) ^ (-(n : ℤ))‖ = ‖s‖ ^ (-(n : ℤ)) := by
    rw [norm_zpow, norm_neg]
  have hprod : ‖(-s) ^ (-(n : ℤ)) * mellin (EulerIter n f) s‖ ≤
      ‖s‖ ^ (-(n : ℤ)) * C0 := by
    rw [norm_mul, hnormz]
    exact mul_le_mul_of_nonneg_left hmellin (by positivity)
  have hsnorm : 1 ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    rw [hsi] at h
    linarith
  have hB : 0 < ‖s‖ ^ n := pow_pos (lt_of_lt_of_le one_pos hsnorm) n
  have hA : (1 + |t|) ^ N ≤ (2 : ℝ) ^ N * ‖s‖ ^ n := by
    have hle : 1 + |t| ≤ 2 * ‖s‖ := by
      have h := Complex.abs_im_le_norm s
      rw [hsi] at h
      linarith
    calc (1 + |t|) ^ N ≤ (2 * ‖s‖) ^ N := pow_le_pow_left₀ (by positivity) hle N
      _ = (2 : ℝ) ^ N * ‖s‖ ^ N := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ N * ‖s‖ ^ n :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hsnorm hNn) (by positivity)
  have hAB : (1 + |t|) ^ N * ‖s‖ ^ (-(n : ℤ)) ≤ (2 : ℝ) ^ N := by
    rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_le_iff₀ hB]
    exact hA
  calc (1 + |t|) ^ N * ‖logMellinContinuation f P ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = (1 + |t|) ^ N * ‖logMellinContinuation f P s‖ := by rw [hs]
    _ = (1 + |t|) ^ N * ‖(-s) ^ (-(n : ℤ)) * mellin (EulerIter n f) s‖ := by rw [heuler]
    _ ≤ (1 + |t|) ^ N * (‖s‖ ^ (-(n : ℤ)) * C0) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = ((1 + |t|) ^ N * ‖s‖ ^ (-(n : ℤ))) * C0 := by rw [mul_assoc]
    _ ≤ (2 : ℝ) ^ N * C0 := mul_le_mul_of_nonneg_right hAB hC0

theorem logMellinContinuation_admissible {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}
    (h : LogMellinPhysical f δ P) :
    LogMellinAdmissible f δ P (logMellinContinuation f P) := by
  refine ⟨h, ?_, ?_, ?_⟩
  · intro s hs
    exact logMellinContinuation_eq_mellin h s hs
  · refine ⟨logMellinHolomorphicPart f P, ?_, ?_⟩
    · intro s hs
      exact logMellinHolomorphicPart_differentiableAt h s hs
    · intro s _ _
      rfl
  · intro u v hu huv N
    exact logMellinContinuation_rapid_vertical_decay h u v hu huv N

namespace LogMellinAdmissible

variable {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}

theorem verticalIntegrable (h : LogMellinAdmissible f δ P H) (c : ℝ) (hc : 0 < c) :
    Complex.VerticalIntegrable H c volume := by
  have hcd : -δ < c := by linarith [h.delta_pos]
  obtain ⟨C, hC0, hdec⟩ := h.rapid_vertical_decay c c hcd le_rfl 2
  have hcont : Continuous (fun t : ℝ => H ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hre : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by simp
    have hne : ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro hz
      have h1 : ((c : ℂ) + (t : ℂ) * Complex.I).re = 0 := by rw [hz]; simp
      have h2 : c = 0 := by simpa [hre] using h1
      linarith
    have hlin : ContinuousAt (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) t :=
      continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
    exact ContinuousAt.comp (g := H) (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) (x := t)
      ((h.differentiableAt _ (by rw [hre]; exact hcd) hne).continuousAt) hlin
  obtain ⟨C1, hC1⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hcont.continuousOn (s := Set.Icc (-1) 1))
  set K : ℝ := 4 * (C + max C1 0) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hstep : ∀ t : ℝ, ((1 + |t|) ^ 2)⁻¹ ≤ (1 + t ^ 2)⁻¹ := by
    intro t
    have hle : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
      nlinarith [abs_nonneg t, sq_abs t, sq_nonneg t]
    simpa only [one_div] using one_div_le_one_div_of_le (show (0 : ℝ) < 1 + t ^ 2 by positivity) hle
  have hcase : ∀ t : ℝ, ‖H ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K * ((1 + |t|) ^ 2)⁻¹ := by
    intro t
    by_cases ht : 1 ≤ |t|
    · have hb := hdec c t le_rfl le_rfl ht
      have hpos : (0 : ℝ) < (1 + |t|) ^ 2 := by positivity
      have h2 : ‖H ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * ((1 + |t|) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]
        linarith [hb]
      refine h2.trans ?_
      have hCK : C ≤ K := by
        rw [hK]; nlinarith [hC0, le_max_right C1 0]
      exact mul_le_mul_of_nonneg_right hCK (by positivity)
    · have ht' : |t| < 1 := not_le.mp ht
      have hb := hC1 t (by
        rw [Set.mem_Icc]
        exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩)
      refine hb.trans ?_
      have h4 : (1 + |t|) ^ 2 ≤ 4 := by
        nlinarith [abs_nonneg t, sq_abs t, sq_nonneg t, le_of_lt ht']
      have hinv : (4 : ℝ)⁻¹ ≤ ((1 + |t|) ^ 2)⁻¹ := by
        simpa only [one_div] using
          one_div_le_one_div_of_le (show (0 : ℝ) < (1 + |t|) ^ 2 by positivity) h4
      have h1 : K * (4 : ℝ)⁻¹ ≤ K * ((1 + |t|) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hK0
      have h2 : K * (4 : ℝ)⁻¹ = C + max C1 0 := by rw [hK]; ring
      calc C1 ≤ max C1 0 := le_max_left _ _
        _ ≤ C + max C1 0 := by linarith [hC0]
        _ = K * (4 : ℝ)⁻¹ := h2.symm
        _ ≤ K * ((1 + |t|) ^ 2)⁻¹ := h1
  have hbound_all : ∀ t : ℝ, ‖H ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K * (1 + t ^ 2)⁻¹ :=
    fun t => (hcase t).trans (mul_le_mul_of_nonneg_left (hstep t) hK0)
  show Integrable (fun y : ℝ => H ((c : ℂ) + (y : ℂ) * Complex.I)) volume
  exact Integrable.mono' (integrable_inv_one_add_sq.const_mul K) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound_all)

end LogMellinAdmissible
end DedekindZetaZeroFree.LargeSieve.Vendor

end
