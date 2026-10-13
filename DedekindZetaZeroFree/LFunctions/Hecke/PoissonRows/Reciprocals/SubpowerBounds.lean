module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.LogarithmicDisks
public import DedekindZetaZeroFree.Analysis.Complex.ThreeCircles
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.EulerBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.ReciprocalPrimitive

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.DetectorDef DedekindZetaZeroFree.Quantitative.DetectorHeight

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem reciprocal_primitive (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧ ∃ Uε : ℝ, 2 ≤ Uε ∧ ∀ U : ℝ, Uε ≤ U →
      ∀ u : D.Row, u.u ≠ 1 → U ≤ D.q u → D.q u < 2 * U → u ∉ exceptionalSet D ρ U →
      ∀ g : ℂ → ℂ, Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F (D.omega u).character s) →
      ∀ s : ℂ, (8801 / 10000 : ℝ) ≤ s.re → |s.im| ≤ 2 * U ^ ρ →
        g s ≠ 0 ∧ ‖(g s)⁻¹‖ ≤ Cε * U ^ ε := by
  classical
  obtain ⟨C₁, hC₁, U₁, hU₁, hdisk⟩ :=
    ReciprocalLogDisk.reciprocal_log_disk D A_F ρ hA hconv hρ
  obtain ⟨C₂, hC₂, heul⟩ := ReciprocalPrimitiveAux.euler_inverse_bound F
  have hr0pos : (0 : ℝ) < ReciprocalLogDisk.r₀ := by norm_num [ReciprocalLogDisk.r₀]
  have hr02 : ReciprocalLogDisk.r₀ < ReciprocalLogDisk.r₂ := by
    norm_num [ReciprocalLogDisk.r₀, ReciprocalLogDisk.r₂]
  have hr1r2 : (11199 / 10000 : ℝ) < ReciprocalLogDisk.r₂ := by
    norm_num [ReciprocalLogDisk.r₂]
  have hr0r1 : ReciprocalLogDisk.r₀ < (11199 / 10000 : ℝ) := by
    norm_num [ReciprocalLogDisk.r₀]
  have hr2R : ReciprocalLogDisk.r₂ < ReciprocalLogDisk.R₀ := by
    norm_num [ReciprocalLogDisk.r₂, ReciprocalLogDisk.R₀]
  have hsub : 0 < Real.log ReciprocalLogDisk.r₂ - Real.log ReciprocalLogDisk.r₀ := by
    have := Real.log_lt_log hr0pos hr02
    linarith
  have hθ0 : 0 ≤ (Real.log (11199 / 10000 : ℝ) - Real.log ReciprocalLogDisk.r₀) /
      (Real.log ReciprocalLogDisk.r₂ - Real.log ReciprocalLogDisk.r₀) := by
    apply div_nonneg _ hsub.le
    have := Real.log_lt_log hr0pos hr0r1
    linarith
  have hθ1 : (Real.log (11199 / 10000 : ℝ) - Real.log ReciprocalLogDisk.r₀) /
      (Real.log ReciprocalLogDisk.r₂ - Real.log ReciprocalLogDisk.r₀) < 1 := by
    rw [div_lt_one hsub]
    have := Real.log_lt_log (by norm_num : (0 : ℝ) < 11199 / 10000) hr1r2
    linarith
  obtain ⟨K, hK0, hK⟩ := ThreeCircles.absorb C₁ _ ε hC₁ hθ0 hθ1 hε
  refine ⟨max C₂ (Real.exp K), lt_max_of_lt_left hC₂, max U₁ 3,
    le_trans hU₁ (le_max_left _ _), ?_⟩
  intro U hU u hu1 hq1 hq2 hex g hg hgL s hs hs_im
  have hU3 : 3 ≤ U := (le_max_right _ _).trans hU
  have hU1' : U₁ ≤ U := (le_max_left _ _).trans hU
  have hUpos : 0 < U := by linarith
  have hUε : 1 ≤ U ^ ε := Real.one_le_rpow (by linarith) hε.le
  have hCmax : 0 ≤ max C₂ (Real.exp K) := le_trans hC₂.le (le_max_left _ _)
  by_cases hσ : (31 / 10 : ℝ) ≤ s.re
  · obtain ⟨h1, h2⟩ := heul (D.omega u) g hg hgL s hσ
    refine ⟨h1, h2.trans ?_⟩
    calc C₂ ≤ max C₂ (Real.exp K) * 1 := by rw [mul_one]; exact le_max_left _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hUε hCmax
  · push_neg at hσ
    obtain ⟨_, ℓ, hℓan, hexp, _, hbig, hsmall⟩ :=
      hdisk U hU1' u hu1 hq1 hq2 hex g hg hgL s.im hs_im
    have hlog1 : 1 ≤ Real.log U := by
      rw [Real.le_log_iff_exp_le hUpos]
      have := Real.exp_one_lt_d9
      norm_num at this
      linarith
    have hsc' : s - ((2 : ℂ) + (s.im : ℂ) * Complex.I) = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    have hsc : s = ((2 : ℂ) + (s.im : ℂ) * Complex.I) + ((s.re - 2 : ℝ) : ℂ) := by
      rw [← hsc']; ring
    have hwle : |s.re - 2| ≤ 11199 / 10000 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hdist : dist s ((2 : ℂ) + (s.im : ℂ) * Complex.I) = |s.re - 2| := by
      rw [dist_eq_norm, hsc', Complex.norm_real, Real.norm_eq_abs]
    have hsball : s ∈ Metric.ball ((2 : ℂ) + (s.im : ℂ) * Complex.I) ReciprocalLogDisk.R₀ := by
      rw [Metric.mem_ball, hdist]
      have : (11199 / 10000 : ℝ) < ReciprocalLogDisk.R₀ := by
        norm_num [ReciprocalLogDisk.R₀]
      linarith
    have hℓs : ‖ℓ s‖ ≤ C₁ * (Real.log U) ^ ((Real.log (11199 / 10000 : ℝ) -
        Real.log ReciprocalLogDisk.r₀) /
      (Real.log ReciprocalLogDisk.r₂ - Real.log ReciprocalLogDisk.r₀)) := by
      by_cases hcase : |s.re - 2| ≤ ReciprocalLogDisk.r₀
      · have h1 := hsmall s (by rw [Metric.mem_closedBall, hdist]; exact hcase)
        refine h1.trans ?_
        have h2 := Real.one_le_rpow hlog1 hθ0
        nlinarith
      · have h := ThreeCircles.three_circles ℓ ((2 : ℂ) + (s.im : ℂ) * Complex.I)
          ReciprocalLogDisk.R₀ ReciprocalLogDisk.r₀ (11199 / 10000 : ℝ) ReciprocalLogDisk.r₂
          hr0pos hr02 hr1r2.le hr2R hℓan.differentiableOn C₁ (Real.log U) hC₁ hlog1
          hsmall hbig (s.re - 2) (not_le.mp hcase) hwle
        rw [← hsc] at h
        exact h
    have hgs : g s = Complex.exp (ℓ s) := hexp s hsball
    refine ⟨by rw [hgs]; exact Complex.exp_ne_zero _, ?_⟩
    rw [hgs, ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
    calc Real.exp (-(ℓ s).re)
        ≤ Real.exp (C₁ * (Real.log U) ^ ((Real.log (11199 / 10000 : ℝ) -
        Real.log ReciprocalLogDisk.r₀) /
      (Real.log ReciprocalLogDisk.r₂ - Real.log ReciprocalLogDisk.r₀))) := by
          apply Real.exp_le_exp.mpr
          have h1 := Complex.abs_re_le_norm (ℓ s)
          have h2 := neg_le_abs ((ℓ s).re)
          linarith
      _ ≤ Real.exp (ε * Real.log U + K) := Real.exp_le_exp.mpr (hK _ hlog1)
      _ = Real.exp K * U ^ ε := by
          rw [Real.rpow_def_of_pos hUpos, ← Real.exp_add]
          congr 1
          ring
      _ ≤ max C₂ (Real.exp K) * U ^ ε :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end

end DedekindZetaZeroFree.Quantitative.ReciprocalPrimitive
