module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.MellinStripInversion
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LogarithmicWeights

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Vendor.LogReflection

def multiplier (D : ℝ) (r : ℕ) (s : ℂ) : ℂ :=
  (D : ℂ) ^ (s - 1 / 2) * Complex.Gammaℂ s ^ r *
    (Complex.Gammaℂ (1 - s))⁻¹ ^ r

def spectrum (D : ℝ) (r : ℕ) (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  multiplier D r s * H (1 - s)

theorem reflection_regularity {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}
    {H : ℂ → ℂ} (D : ℝ) (r : ℕ) (hD : 0 < D) (hr : 1 ≤ r)
    (h : LogMellinAdmissible f δ P H) :
    (∀ s : ℂ, 1 < s.re → s.re < 1 + δ →
      DifferentiableAt ℂ (spectrum D r H) s) ∧
    (∀ u v : ℝ, 1 < u → u ≤ v → v < 1 + δ → ∀ N : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, u ≤ σ → σ ≤ v → 1 ≤ |t| →
        (1 + |t|) ^ N * ‖spectrum D r H ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C) := by
  have hform : spectrum D r H = fun s : ℂ =>
      (D : ℂ) ^ (s - 1 / 2) * gammaQuotient r s * H (1 - s) := by
    funext s
    simp only [spectrum, multiplier, gammaQuotient, mul_assoc]
  rw [hform]
  constructor
  · intro s hs hsδ
    have hq : DifferentiableAt ℂ (gammaQuotient r) s :=
      (gammaQuotient_differentiableOn r).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (show 0 < s.re by linarith))
    have harg : -δ < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hne : 1 - s ≠ 0 := by
      intro he
      have := congrArg Complex.re he
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
      linarith
    have hH := (h.differentiableAt (1 - s) harg hne).comp s
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)
    have hp : DifferentiableAt ℂ (fun z : ℂ => (D : ℂ) ^ (z - 1 / 2)) s :=
      (differentiableAt_id.sub (differentiableAt_const (1 / 2 : ℂ))).const_cpow
        (Or.inl (by exact_mod_cast hD.ne'))
    exact (hp.mul hq).mul hH
  · intro u v hu huv hv N
    obtain ⟨Cq, k, hCq, hq⟩ := gammaQuotient_polynomial_bound
      (show 0 < u by linarith) huv r
    obtain ⟨Ch, hCh, hH⟩ := h.rapid_vertical_decay (1 - v) (1 - u)
      (by linarith) (by linarith) (N + k)
    let B : ℝ := Real.rpow D (u - 1 / 2) + Real.rpow D (v - 1 / 2)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    refine ⟨B * Cq * Ch, by positivity, ?_⟩
    intro σ t hσ hσv ht
    let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
    have hsre : s.re = σ := by simp [s]
    have hsim : s.im = t := by simp [s]
    have hp : ‖(D : ℂ) ^ (s - 1 / 2)‖ ≤ B := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]
      have hre : (s - 1 / 2).re = σ - 1 / 2 := by simp [hsre]
      rw [hre]
      by_cases hD1 : 1 ≤ D
      · have hb := Real.rpow_le_rpow_of_exponent_le hD1
          (show σ - 1 / 2 ≤ v - 1 / 2 by linarith)
        dsimp [B]
        exact hb.trans (le_add_of_nonneg_left (by positivity))
      · have hb := Real.rpow_le_rpow_of_exponent_ge hD (le_of_not_ge hD1)
          (show u - 1 / 2 ≤ σ - 1 / 2 by linarith)
        dsimp [B]
        exact hb.trans (le_add_of_nonneg_right (by positivity))
    have hg : ‖gammaQuotient r s‖ ≤ Cq * (1 + |t|) ^ k := by
      rw [gammaQuotient_eq_div]
      simpa only [hsim] using hq s (by simpa [hsre] using hσ)
        (by simpa [hsre] using hσv)
    have heq : 1 - s = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [s] <;> ring
    have hh : (1 + |t|) ^ (N + k) * ‖H (1 - s)‖ ≤ Ch := by
      rw [heq]
      simpa only [abs_neg] using hH (1 - σ) (-t) (by linarith) (by linarith)
        (by simpa only [abs_neg] using ht)
    change (1 + |t|) ^ N * ‖(D : ℂ) ^ (s - 1 / 2) * gammaQuotient r s * H (1 - s)‖ ≤ _
    rw [norm_mul, norm_mul]
    calc
      (1 + |t|) ^ N *
          (‖(D : ℂ) ^ (s - 1 / 2)‖ * ‖gammaQuotient r s‖ * ‖H (1 - s)‖)
          ≤ (1 + |t|) ^ N * (B * (Cq * (1 + |t|) ^ k) * ‖H (1 - s)‖) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul hp hg (norm_nonneg _) hB) (norm_nonneg _)) (by positivity)
      _ = B * Cq * ((1 + |t|) ^ (N + k) * ‖H (1 - s)‖) := by
        rw [pow_add]
        ring
      _ ≤ B * Cq * Ch := mul_le_mul_of_nonneg_left hh (by positivity)

end DedekindZetaZeroFree.LargeSieve.Vendor.LogReflection

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace DedekindZetaZeroFree.LargeSieve.Vendor

def logReflectionMultiplier (D : ℝ) (r : ℕ) (s : ℂ) : ℂ :=
  (D : ℂ) ^ (s - 1 / 2) * Complex.Gammaℂ s ^ r *
    (Complex.Gammaℂ (1 - s))⁻¹ ^ r

def reflectedLogSpectrum (D : ℝ) (r : ℕ) (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  logReflectionMultiplier D r s * H (1 - s)

def reflectedLogDual (D : ℝ) (r : ℕ) (H : ℂ → ℂ) (δ x : ℝ) : ℂ :=
  if 0 < x then mellinInv (1 + δ / 2) (reflectedLogSpectrum D r H) x else 0

variable {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}

private theorem reflected_regularity (D : ℝ) (r : ℕ)
    (hD : 0 < D) (hr : 1 ≤ r) (h : LogMellinAdmissible f δ P H) :
    (∀ s : ℂ, 1 < s.re → s.re < 1 + δ →
      DifferentiableAt ℂ (reflectedLogSpectrum D r H) s) ∧
    (∀ u v : ℝ, 1 < u → u ≤ v → v < 1 + δ → ∀ N : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, u ≤ σ → σ ≤ v → 1 ≤ |t| →
        (1 + |t|) ^ N *
          ‖reflectedLogSpectrum D r H ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C) := by
  exact LogReflection.reflection_regularity D r hD hr h

theorem reflectedLogSpectrum_differentiableOn (D : ℝ) (r : ℕ)
    (hD : 0 < D) (hr : 1 ≤ r) (h : LogMellinAdmissible f δ P H) :
    DifferentiableOn ℂ (reflectedLogSpectrum D r H)
      {s : ℂ | 1 < s.re ∧ s.re < 1 + δ} := by
  intro s hs
  exact ((reflected_regularity D r hD hr h).1 s hs.1 hs.2).differentiableWithinAt

theorem reflectedLogSpectrum_verticalIntegrable (D : ℝ) (r : ℕ)
    (hD : 0 < D) (hr : 1 ≤ r) (h : LogMellinAdmissible f δ P H)
    (c : ℝ) (hc : 1 < c) (hcδ : c < 1 + δ) :
    Complex.VerticalIntegrable (reflectedLogSpectrum D r H) c volume := by
  obtain ⟨hhol, hrapid⟩ := reflected_regularity D r hD hr h
  exact (LogReflection.strip_integrability (reflectedLogSpectrum D r H)
    1 (1 + δ) hhol hrapid c hc hcδ).1

theorem reflectedLogDual_eq_mellinInv (D : ℝ) (r : ℕ)
    (hD : 0 < D) (hr : 1 ≤ r) (h : LogMellinAdmissible f δ P H)
    (c x : ℝ) (hc : 1 < c) (hcδ : c < 1 + δ) (hx : 0 < x) :
    reflectedLogDual D r H δ x = mellinInv c (reflectedLogSpectrum D r H) x := by
  obtain ⟨hhol, hrapid⟩ := reflected_regularity D r hD hr h
  have hδ := h.delta_pos
  rw [reflectedLogDual, if_pos hx]
  exact (LogReflection.strip_inverse_api (reflectedLogSpectrum D r H)
    1 (1 + δ) hhol hrapid).1 (1 + δ / 2) c x
    (by linarith) (by linarith) hc hcδ hx

end DedekindZetaZeroFree.LargeSieve.Vendor

end

end
