module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.FrequencyHeightPrefix
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.LogarithmicDisks

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawReciprocalLogDisk31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31
open DedekindZetaZeroFree.Quantitative.ReciprocalLogDisk DedekindZetaZeroFree.Quantitative.ReciprocalLogDiskAux
open DedekindZetaZeroFree.Quantitative.DetectorDef
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem nonvanishing_of_not_exceptional (ρ U : ℝ) (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (hUq : U ≤ frequencyNorm D.recipe u)
    (hUq2 : frequencyNorm D.recipe u < 2 * U) (hex : u ∉ FixedData.rawExceptionalSet D ρ U)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hgL : ∀ s : ℂ, 1 < s.re →
      g s = Detector.idealLSeries F (FixedData.primMinus D u).character s)
    (s : ℂ) (h1 : σ₀ ≤ s.re) (h2 : |s.im| ≤ 4 * U ^ ρ) : g s ≠ 0 := by
  intro h0
  have hs0 : 0 < s.re := by
    have : (0 : ℝ) < σ₀ := by unfold σ₀; norm_num
    linarith
  exact hex ⟨hu, hUq, hUq2, s, ⟨hs0, g, fun z _ => hg.analyticAt z, hgL, h0⟩, h1, h2⟩

theorem zero_at_one (ρ U : ℝ) (hρ : 0 < ρ) (hU : 1 ≤ U) (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (hUq : U ≤ frequencyNorm D.recipe u)
    (hUq2 : frequencyNorm D.recipe u < 2 * U) (hex : u ∉ FixedData.rawExceptionalSet D ρ U)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hgL : ∀ s : ℂ, 1 < s.re →
      g s = Detector.idealLSeries F (FixedData.primMinus D u).character s) :
    g 1 ≠ 0 := by
  refine nonvanishing_of_not_exceptional D ρ U u hu hUq hUq2 hex g hg hgL 1 ?_ ?_
  · simp [σ₀]; norm_num
  · have : (0 : ℝ) ≤ U ^ ρ := Real.rpow_nonneg (by linarith) _
    simp; linarith

theorem raw_reciprocal_log_disk (A ρ : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (hρ : HeightSpec D A ρ) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
        u ∉ FixedData.rawExceptionalSet D ρ U →
      ∀ g : ℂ → ℂ, Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re →
          g s = Detector.idealLSeries F (FixedData.primMinus D u).character s) →
      ∀ t : ℝ, |t| ≤ 2 * U ^ ρ →
        Metric.ball ((2 : ℂ) + (t : ℂ) * Complex.I) R₀ ⊆
          {s : ℂ | σ₀ < s.re ∧ |s.im| < 4 * U ^ ρ} ∧
        ∃ ℓ : ℂ → ℂ,
          AnalyticOnNhd ℂ ℓ (Metric.ball ((2 : ℂ) + (t : ℂ) * Complex.I) R₀) ∧
          (∀ s ∈ Metric.ball ((2 : ℂ) + (t : ℂ) * Complex.I) R₀, g s = Complex.exp (ℓ s)) ∧
          ℓ ((2 : ℂ) + (t : ℂ) * Complex.I) =
            eulerLog (FixedData.primMinus D u) ((2 : ℂ) + (t : ℂ) * Complex.I) ∧
          (∀ s ∈ Metric.closedBall ((2 : ℂ) + (t : ℂ) * Complex.I) r₂,
            ‖ℓ s‖ ≤ C * Real.log U) ∧
          (∀ s ∈ Metric.closedBall ((2 : ℂ) + (t : ℂ) * Complex.I) r₀, ‖ℓ s‖ ≤ C) := by
  obtain ⟨E, hE, hEf⟩ := euler_log_facts F
  obtain ⟨C₃, hC₃, H3⟩ := hconv.2.2 1 one_pos
  obtain ⟨U₀, hU₀2, hdisk⟩ := disk_subset_zero_free_region ρ hρ.1
  have hR₀ : R₀ = 111995 / 100000 := rfl
  have hr₂ : r₂ = 1119925 / 1000000 := rfl
  have hr₀ : r₀ = 999 / 1000 := rfl
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC₁ : 0 < C₃ * 6 ^ A := mul_pos hC₃ (Real.rpow_pos_of_pos (by norm_num) _)
  set lc : ℝ := |Real.log (C₃ * 6 ^ A)| with hlc
  have hlc0 : 0 ≤ lc := abs_nonneg _
  set a : ℝ := 2 * r₂ / (R₀ - r₂) with ha
  set b : ℝ := (R₀ + r₂) / (R₀ - r₂) with hb_def
  have ha0 : 0 ≤ a := by rw [ha, hR₀, hr₂]; norm_num
  have hb0 : 0 ≤ b := by rw [hb_def, hR₀, hr₂]; norm_num
  set c1 : ℝ := 1 / Real.log 2 with hc1
  have hc10 : 0 ≤ c1 := by rw [hc1]; exact div_nonneg zero_le_one hlog2.le
  set K : ℝ := 1 / 10 + 1 + ρ * A with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; have : 0 ≤ ρ * A := mul_nonneg hρ.1.le hA
    linarith
  have hCpos : 0 ≤ a * (lc * c1 + K) + b * E * c1 :=
    add_nonneg (mul_nonneg ha0 (add_nonneg (mul_nonneg hlc0 hc10) hK0))
      (mul_nonneg (mul_nonneg hb0 hE.le) hc10)
  refine ⟨a * (lc * c1 + K) + b * E * c1 + E, by linarith, U₀, hU₀2, fun U hU u hu1 hUq hUq2 hu g hg hgL t ht => ?_⟩
  have hU2 : 2 ≤ U := le_trans hU₀2 hU
  have hUpos : 0 < U := by linarith
  have hsub := hdisk U hU t ht
  refine ⟨hsub, ?_⟩
  set c : ℂ := (2 : ℂ) + (t : ℂ) * Complex.I with hcdef
  have hcre : c.re = 2 := by simp [hcdef]
  have hre' : ∀ s : ℂ, |s.re - 2| ≤ ‖s - c‖ := by
    intro s
    have h1 : (s - c).re = s.re - 2 := by simp [hcdef]
    rw [← h1]
    exact Complex.abs_re_le_norm _
  have hgan : AnalyticOnNhd ℂ g (Metric.ball c R₀) := fun z _ => hg.analyticAt z
  have hUρ : (1 : ℝ) ≤ U ^ ρ := Real.one_le_rpow (by linarith) hρ.1.le
  have hgrow : ∀ s : ℂ, 4 / 5 ≤ s.re → s.re ≤ 4 → |s.im| ≤ 4 * U ^ ρ →
      ‖g s‖ ≤ C₃ * 6 ^ A * U ^ K := by
    intro s h1 h2 h3
    have hI := H3 u hu1 U hU2 hUq hUq2 g hg hgL s.re h1 h2 s.im
    rw [Complex.re_add_im] at hI
    have hpow : (2 + |s.im|) ^ A ≤ 6 ^ A * U ^ (ρ * A) := by
      calc (2 + |s.im|) ^ A ≤ (6 * U ^ ρ) ^ A :=
            Real.rpow_le_rpow (by positivity) (by linarith) hA
        _ = 6 ^ A * U ^ (ρ * A) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hUpos.le]
    calc ‖g s‖ ≤ C₃ * U ^ ((1:ℝ) / 10 + 1) * (2 + |s.im|) ^ A := hI
      _ ≤ C₃ * U ^ ((1:ℝ) / 10 + 1) * (6 ^ A * U ^ (ρ * A)) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg hC₃.le (Real.rpow_nonneg hUpos.le _))
      _ = C₃ * 6 ^ A * U ^ K := by
          rw [hK, Real.rpow_add hUpos ((1:ℝ) / 10 + 1) (ρ * A)]; ring
  have hnz : ∀ s ∈ Metric.ball c R₀, g s ≠ 0 := by
    intro s hs
    have hs' := hsub hs
    exact nonvanishing_of_not_exceptional D ρ U u hu1 hUq hUq2 hu g hg hgL s hs'.1.le hs'.2.le
  obtain ⟨hEan, hEexp, hEbd⟩ := hEf (FixedData.primMinus D u)
  have hc1' : 1 < c.re := by rw [hcre]; norm_num
  have hcexp : Complex.exp (eulerLog (FixedData.primMinus D u) c) = g c := by
    rw [hgL c hc1']
    exact hEexp c hc1'
  obtain ⟨ℓ, hℓan, hℓexp, hℓc⟩ :=
    exists_analytic_log_ball hgan hnz hcexp (by rw [hR₀]; norm_num)
  have hEc : ‖eulerLog (FixedData.primMinus D u) c‖ ≤ E := by
    apply hEbd
    rw [hcre]; norm_num
  have hlogU : Real.log 2 ≤ Real.log U := Real.log_le_log (by norm_num) hU2
  have hlogU0 : 0 ≤ Real.log U := le_trans hlog2.le hlogU
  refine ⟨ℓ, hℓan, hℓexp, hℓc, ?_, ?_⟩
  ·
    have hM : ∀ s ∈ Metric.ball c R₀, (ℓ s).re ≤ lc + K * Real.log U := by
      intro s hs
      have hs' := hsub hs
      have hsn : ‖s - c‖ < R₀ := by
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hs
      have h1 := hre' s
      have hsre := abs_lt.mp (lt_of_le_of_lt h1 hsn)
      have hb : ‖g s‖ ≤ C₃ * 6 ^ A * U ^ K :=
        hgrow s (by rw [hR₀] at hsre; linarith [hsre.1]) (by rw [hR₀] at hsre; linarith [hsre.2])
          (by linarith [hs'.2])
      have hnorm : ‖g s‖ = Real.exp (ℓ s).re := by
        rw [hℓexp s hs, Complex.norm_exp]
      have hpos : 0 < C₃ * 6 ^ A * U ^ K := mul_pos hC₁ (Real.rpow_pos_of_pos hUpos _)
      have hle : (ℓ s).re ≤ Real.log (C₃ * 6 ^ A * U ^ K) := by
        rw [Real.le_log_iff_exp_le hpos, ← hnorm]; exact hb
      rw [Real.log_mul hC₁.ne' (Real.rpow_pos_of_pos hUpos _).ne', Real.log_rpow hUpos] at hle
      have : Real.log (C₃ * 6 ^ A) ≤ lc := le_abs_self _
      linarith
    have hM0 : 0 ≤ lc + K * Real.log U := add_nonneg hlc0 (mul_nonneg hK0 hlogU0)
    have hBC := borel_caratheodory (c := c) (r := r₂) (R := R₀) (by rw [hr₂]; norm_num)
      (by rw [hr₂, hR₀]; norm_num) hM0 hℓan hM
    intro s hs
    refine le_trans (hBC s hs) ?_
    rw [hℓc]
    have hL1 : 1 ≤ c1 * Real.log U := by
      rw [hc1, one_div, inv_mul_eq_div, le_div_iff₀ hlog2]; linarith
    have h1 : a * lc * 1 ≤ a * lc * (c1 * Real.log U) :=
      mul_le_mul_of_nonneg_left hL1 (mul_nonneg ha0 hlc0)
    have h2 : b * E * 1 ≤ b * E * (c1 * Real.log U) :=
      mul_le_mul_of_nonneg_left hL1 (mul_nonneg hb0 hE.le)
    have h3 : 0 ≤ E * Real.log U := mul_nonneg hE.le hlogU0
    have h4 : b * ‖eulerLog (FixedData.primMinus D u) c‖ ≤ b * E :=
      mul_le_mul_of_nonneg_left hEc hb0
    nlinarith
  ·
    have hsub1 : Metric.ball c 1 ⊆ Metric.ball c R₀ :=
      Metric.ball_subset_ball (by rw [hR₀]; norm_num)
    have hEan' : AnalyticOnNhd ℂ (eulerLog (FixedData.primMinus D u)) (Metric.ball c 1) := by
      refine AnalyticOnNhd.mono hEan ?_
      intro s hs
      have hsn : ‖s - c‖ < 1 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hs
      have h1 := hre' s
      have := abs_lt.mp (lt_of_le_of_lt h1 hsn)
      show 1 < s.re
      linarith [this.1]
    have huniq := analytic_log_unique_ball (c := c) (R := 1) (ℓ₁ := ℓ)
      (ℓ₂ := eulerLog (FixedData.primMinus D u)) one_pos (hℓan.mono hsub1) hEan'
      (fun s hs => by
        have hs1 : 1 < s.re := by
          have hsn : ‖s - c‖ < 1 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hs
          have h1 := hre' s
          have := abs_lt.mp (lt_of_le_of_lt h1 hsn)
          linarith [this.1]
        rw [← hℓexp s (hsub1 hs), hgL s hs1]
        exact (hEexp s hs1).symm) hℓc
    intro s hs
    have hs1 : s ∈ Metric.ball c 1 :=
      Metric.closedBall_subset_ball (by rw [hr₀]; norm_num) hs
    rw [huniq s hs1]
    refine le_trans (hEbd s ?_) (by linarith)
    have hsn : ‖s - c‖ ≤ r₀ := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hs
    have h1 := hre' s
    have := abs_le.mp (le_trans h1 hsn)
    rw [hr₀] at this
    linarith [this.1]

end

end DedekindZetaZeroFree.Quantitative.RawReciprocalLogDisk31
