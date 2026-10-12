module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.GaussianMellinContourShift

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace DedekindZetaZeroFree

open MeasureTheory
open scoped FourierTransform

private lemma reflected_norm (G : ℂ → ℂ) (c t : ℝ) :
    G (-(((-c : ℝ) : ℂ) + t * Complex.I)) = G ((c : ℂ) + (-t) * Complex.I) := by
  congr 1
  push_cast
  ring

private lemma line_integrable (G : ℂ → ℂ)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 < s.re})
    (hdecay : ∀ a b : ℝ, 1 < a → a ≤ b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Icc a b, ∀ t : ℝ,
        ‖G ((r : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2))
    (c : ℝ) (hc : 1 < c) :
    Integrable (fun t : ℝ => G (-(((-c : ℝ) : ℂ) + t * Complex.I))) := by
  obtain ⟨C, hC, hbound⟩ := hdecay c c hc le_rfl
  have hcont : Continuous (fun t : ℝ => G ((c : ℂ) + (-t) * Complex.I)) := by
    apply hG.continuousOn.comp_continuous
    · fun_prop
    · intro t
      simpa using hc
  simp_rw [reflected_norm]
  refine (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable ?_
  filter_upwards [] with t
  simpa [div_eq_mul_inv] using hbound c ⟨le_rfl, le_rfl⟩ (-t)

private lemma inverse_bound (G : ℂ → ℂ) (c C : ℝ)
    (hbound : ∀ t : ℝ, ‖G ((c : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2))
    (x : ℝ) (hx : 0 < x) :
    ‖mellinInv (-c) (fun z : ℂ => G (-z)) x‖ ≤
      (‖(1 / (2 * Real.pi) : ℝ)‖ * (C * ∫ t : ℝ, (1 + t ^ 2)⁻¹)) * x ^ c := by
  have hnorm (t : ℝ) : ‖(x : ℂ) ^ (-(((-c : ℝ) : ℂ) + t * Complex.I))‖ = x ^ c := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have hb : ‖∫ t : ℝ, (x : ℂ) ^ (-(((-c : ℝ) : ℂ) + t * Complex.I)) •
      G (-(((-c : ℝ) : ℂ) + t * Complex.I))‖ ≤
      ∫ t : ℝ, (x ^ c * C) * (1 + t ^ 2)⁻¹ := by
    apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul (x ^ c * C))
    filter_upwards [] with t
    rw [norm_smul, hnorm, reflected_norm G c t]
    have := mul_le_mul_of_nonneg_left (hbound (-t)) (Real.rpow_nonneg hx.le c)
    simpa [div_eq_mul_inv, mul_assoc] using this
  rw [mellinInv, norm_smul]
  calc
    _ ≤ ‖(1 / (2 * Real.pi) : ℝ)‖ * (∫ t : ℝ, (x ^ c * C) * (1 + t ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by rw [integral_const_mul]; ring

set_option maxHeartbeats 1000000 in

theorem mellin_right_shift_flat
    (G : ℂ → ℂ) (g : ℝ → ℂ)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 < s.re})
    (hdecay : ∀ a b : ℝ, 1 < a → a ≤ b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Icc a b, ∀ t : ℝ,
        ‖G ((r : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2))
    (hinv : ∀ x : ℝ, 0 < x →
      g x = mellinInv (-2) (fun z : ℂ => G (-z)) x) :
    ContinuousOn g (Set.Ioi (0 : ℝ)) ∧
    MeasureTheory.LocallyIntegrableOn g (Set.Ioi (0 : ℝ)) ∧
    (∀ b : ℝ, g =O[nhdsWithin 0 (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Real.rpow x b)) ∧
    (∀ c : ℝ, 2 < c → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, 0 < x → x ≤ 1 → ‖g x‖ ≤ C * Real.rpow x c) := by
  have hcont : ContinuousOn g (Set.Ioi (0 : ℝ)) := by
    let H : ℝ → ℂ := fun y => G (-(((-2 : ℝ) : ℂ) + ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I))
    have hH : Integrable H :=
      (line_integrable G hG hdecay 2 (by norm_num)).comp_mul_left'
        (R := 2 * Real.pi) (by positivity)
    have hfourier : Continuous (𝓕 H) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hH
    intro x hx
    have hp : ContinuousAt (fun x : ℝ => (x : ℂ) ^ ((2 : ℝ) : ℂ)) x :=
      Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (ne_of_gt hx))
    have hl : ContinuousAt (fun x : ℝ => Real.log x) x :=
      Real.continuousAt_log (ne_of_gt hx)
    have hh := hp.smul (hfourier.continuousAt.comp hl)
    apply hh.continuousWithinAt.congr
    · intro y hy
      rw [hinv y hy, mellinInv_eq_fourierInv _ _ hy, Real.fourierInv_eq_fourier_neg]
      simp only [neg_neg]
      simp [H, Function.comp_def, Complex.ofReal_mul]
    · rw [hinv x hx, mellinInv_eq_fourierInv _ _ hx, Real.fourierInv_eq_fourier_neg]
      simp only [neg_neg]
      simp [H, Function.comp_def, Complex.ofReal_mul]
  have hquant : ∀ c : ℝ, 2 < c → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, 0 < x → x ≤ 1 → ‖g x‖ ≤ C * x ^ c := by
    intro c hc
    obtain ⟨C, hC, hb⟩ := hdecay c c (by linarith) le_rfl
    refine ⟨‖(1 / (2 * Real.pi) : ℝ)‖ * (C * ∫ t : ℝ, (1 + t ^ 2)⁻¹), ?_, ?_⟩
    · exact mul_nonneg (norm_nonneg _) (mul_nonneg hC (integral_nonneg (fun t => by positivity)))
    · intro x hx _
      rw [(mellin_gaussian_contour_shift G g hG hdecay hinv c (by linarith) x hx).1]
      exact inverse_bound G c C (hb c ⟨le_rfl, le_rfl⟩) x hx
  refine ⟨hcont, hcont.locallyIntegrableOn measurableSet_Ioi, ?_, hquant⟩
  intro b
  obtain ⟨C, hC, hb⟩ := hquant (max 2 b + 1) (by have := le_max_left 2 b; linarith)
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  have hsmall : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), x ≤ 1 :=
    (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_mem_nhdsWithin, hsmall] with x hx hx1
  change ‖g x‖ ≤ C * ‖(x ^ b : ℝ)‖
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hx) b)]
  exact (hb x hx hx1).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by have := le_max_right 2 b; linarith)) hC)

end DedekindZetaZeroFree
