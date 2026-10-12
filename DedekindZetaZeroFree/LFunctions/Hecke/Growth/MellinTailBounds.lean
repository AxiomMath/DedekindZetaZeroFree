module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import DedekindZetaZeroFree.Analysis.Decay.PowerStretchedExponentialEnvelope
public import DedekindZetaZeroFree.LFunctions.Hecke.Growth.StretchedExponentialExponent

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

open MeasureTheory

private theorem tail_decay_integrable (a p : ℝ) (ha : 0 < a) (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => Real.exp (-(a / 2) * t ^ p)) (Set.Ioi (1 : ℝ)) volume := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (b := a / 2)
    (by norm_num) hp (by positivity)
  simp only [Real.rpow_zero, one_mul] at hi
  exact hi.mono_set (fun t ht => by simp only [Set.mem_Ioi] at *; linarith)

private theorem tail_norm_envelope (h : ℝ → ℂ) (A a p : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (hp : 0 < p)
    (hdecay : ∀ t : ℝ, 1 ≤ t → ‖h t‖ ≤ A * Real.exp (-a * t ^ p))
    (z : ℂ) (R : ℝ) (hR : 0 ≤ R) (hz : z.re - 1 ≤ R)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖(t : ℂ) ^ (z - 1) * h t‖ ≤
      (A * Real.exp ((R / p) * Real.log (2 + 2 * R / (a * p)))) *
        Real.exp (-(a / 2) * t ^ p) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < t)]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    t ^ (z.re - 1) * ‖h t‖ ≤ t ^ R * (A * Real.exp (-a * t ^ p)) :=
      mul_le_mul (Real.rpow_le_rpow_of_exponent_le ht hz) (hdecay t ht)
        (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)
    _ = A * (t ^ R * Real.exp (-a * t ^ p)) := by ring
    _ ≤ A * (Real.exp ((R / p) * Real.log (2 + 2 * R / (a * p))) *
        Real.exp (-(a / 2) * t ^ p)) :=
      mul_le_mul_of_nonneg_left (power_mul_stretchedExp_le a p ha hp R hR t ht) hA
    _ = _ := by ring

private theorem tail_integrand_measurable (h : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Set.Ioi (1 : ℝ)))) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (z - 1) * h t)
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
  refine ((continuousOn_of_forall_continuousAt ?_).aestronglyMeasurable
    measurableSet_Ioi).mul hmeas
  intro t ht
  exact Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (by
    simp only [Set.mem_Ioi] at ht
    linarith))

theorem mellinTail_integrable_of_stretchedExp (h : ℝ → ℂ) (A a p : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (hp : 0 < p)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Set.Ioi (1 : ℝ))))
    (hdecay : ∀ t : ℝ, 1 ≤ t → ‖h t‖ ≤ A * Real.exp (-a * t ^ p))
    (z : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * h t)
      (Set.Ioi (1 : ℝ)) volume := by
  let R := max 0 (z.re - 1)
  have hi := (tail_decay_integrable a p ha hp).const_mul
    (A * Real.exp ((R / p) * Real.log (2 + 2 * R / (a * p))))
  refine hi.mono' (tail_integrand_measurable h hmeas z) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact tail_norm_envelope h A a p hA ha hp hdecay z R (le_max_left _ _)
    (le_max_right _ _) t (le_of_lt ht)

theorem mellinTail_norm_le (h : ℝ → ℂ) (A a p : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (hp : 0 < p)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Set.Ioi (1 : ℝ))))
    (hdecay : ∀ t : ℝ, 1 ≤ t → ‖h t‖ ≤ A * Real.exp (-a * t ^ p)) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ (z : ℂ) (R : ℝ), 0 ≤ R → z.re - 1 ≤ R →
        ‖∫ t : ℝ in Set.Ioi (1 : ℝ), (t : ℂ) ^ (z - 1) * h t‖ ≤
          C * Real.exp (K * (1 + R) * Real.log (2 + R)) := by
  let J : ℝ := ∫ t : ℝ in Set.Ioi (1 : ℝ), Real.exp (-(a / 2) * t ^ p)
  have hJ : 0 ≤ J := integral_nonneg (fun t => (Real.exp_pos _).le)
  obtain ⟨K, hK, hKbound⟩ := stretchedExp_envelope_exponent_le a p ha hp
  refine ⟨A * J, K, mul_nonneg hA hJ, hK, ?_⟩
  intro z R hR hz
  have hi := mellinTail_integrable_of_stretchedExp h A a p hA ha hp hmeas hdecay z
  have hb := (tail_decay_integrable a p ha hp).const_mul
    (A * Real.exp ((R / p) * Real.log (2 + 2 * R / (a * p))))
  calc
    ‖∫ t : ℝ in Set.Ioi (1 : ℝ), (t : ℂ) ^ (z - 1) * h t‖ ≤
        ∫ t : ℝ in Set.Ioi (1 : ℝ), ‖(t : ℂ) ^ (z - 1) * h t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Set.Ioi (1 : ℝ),
        (A * Real.exp ((R / p) * Real.log (2 + 2 * R / (a * p)))) *
          Real.exp (-(a / 2) * t ^ p) := by
      apply integral_mono_ae hi.norm hb
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact tail_norm_envelope h A a p hA ha hp hdecay z R hR hz t (le_of_lt ht)
    _ = (A * J) * Real.exp ((R / p) * Real.log (2 + 2 * R / (a * p))) := by
      rw [integral_const_mul]
      dsimp [J]
      ring
    _ ≤ (A * J) * Real.exp (K * (1 + R) * Real.log (2 + R)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hKbound R hR)) (mul_nonneg hA hJ)

end DedekindZetaZeroFree.Hecke
