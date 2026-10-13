module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Height
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.LogarithmicDiskBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.ReciprocalLogDisk

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.DetectorDef DedekindZetaZeroFree.Quantitative.DetectorHeight
open DedekindZetaZeroFree.Quantitative.ReciprocalLogDiskAux
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def R₀ : ℝ := 111995 / 100000

def r₂ : ℝ := 1119925 / 1000000

def r₀ : ℝ := 999 / 1000

def eulerLog (ω : Detector.PrimitiveFrequencyCharacter F) (s : ℂ) : ℂ :=
  ∑' P : {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥},
    ∑' k : ℕ, ω.character (P.1 ^ (k + 1)) /
      (((k : ℂ) + 1) * (Ideal.absNorm P.1 : ℂ) ^ (((k : ℂ) + 1) * s))

theorem disk_subset_zero_free_region (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ t : ℝ, |t| ≤ 2 * U ^ ρ →
      Metric.ball ((2 : ℂ) + (t : ℂ) * Complex.I) R₀ ⊆
        {s : ℂ | σ₀ < s.re ∧ |s.im| < 4 * U ^ ρ} := by
  refine ⟨2, le_refl _, fun U hU t ht s hs => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hs
  have hre : |(s - ((2 : ℂ) + (t : ℂ) * Complex.I)).re| < R₀ :=
    lt_of_le_of_lt (Complex.abs_re_le_norm _) hs
  have him : |(s - ((2 : ℂ) + (t : ℂ) * Complex.I)).im| < R₀ :=
    lt_of_le_of_lt (Complex.abs_im_le_norm _) hs
  have e1 : (s - ((2 : ℂ) + (t : ℂ) * Complex.I)).re = s.re - 2 := by simp
  have e2 : (s - ((2 : ℂ) + (t : ℂ) * Complex.I)).im = s.im - t := by simp
  rw [e1] at hre
  rw [e2] at him
  have hR : R₀ = 111995 / 100000 := rfl
  rw [hR] at hre him
  have hU1 : (1 : ℝ) ≤ U ^ ρ := Real.one_le_rpow (by linarith) hρ.le
  obtain ⟨h1, h2⟩ := abs_lt.mp hre
  obtain ⟨h3, h4⟩ := abs_lt.mp him
  obtain ⟨h5, h6⟩ := abs_le.mp ht
  refine ⟨?_, ?_⟩
  · unfold σ₀
    linarith
  · rw [abs_lt]
    constructor <;> linarith

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem reciprocal_log_disk (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ u : D.Row, u.u ≠ 1 → U ≤ D.q u → D.q u < 2 * U → u ∉ exceptionalSet D ρ U →
      ∀ g : ℂ → ℂ, Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F (D.omega u).character s) →
      ∀ t : ℝ, |t| ≤ 2 * U ^ ρ →
        Metric.ball ((2 : ℂ) + (t : ℂ) * Complex.I) R₀ ⊆
          {s : ℂ | σ₀ < s.re ∧ |s.im| < 4 * U ^ ρ} ∧
        ∃ ℓ : ℂ → ℂ,
          AnalyticOnNhd ℂ ℓ (Metric.ball ((2 : ℂ) + (t : ℂ) * Complex.I) R₀) ∧
          (∀ s ∈ Metric.ball ((2 : ℂ) + (t : ℂ) * Complex.I) R₀, g s = Complex.exp (ℓ s)) ∧
          ℓ ((2 : ℂ) + (t : ℂ) * Complex.I) =
            eulerLog (D.omega u) ((2 : ℂ) + (t : ℂ) * Complex.I) ∧
          (∀ s ∈ Metric.closedBall ((2 : ℂ) + (t : ℂ) * Complex.I) r₂,
            ‖ℓ s‖ ≤ C * Real.log U) ∧
          (∀ s ∈ Metric.closedBall ((2 : ℂ) + (t : ℂ) * Complex.I) r₀, ‖ℓ s‖ ≤ C) := by
  obtain ⟨E, hE, hEf⟩ := euler_log_facts F
  obtain ⟨C₁, K, hC₁, hK, hconv'⟩ := convexity_upper_bound D ρ hρ.1
  obtain ⟨U₀, hU₀2, hdisk⟩ := disk_subset_zero_free_region ρ hρ.1
  have hR₀ : R₀ = 111995 / 100000 := rfl
  have hr₂ : r₂ = 1119925 / 1000000 := rfl
  have hr₀ : r₀ = 999 / 1000 := rfl
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set lc : ℝ := |Real.log C₁| with hlc
  set a : ℝ := 2 * r₂ / (R₀ - r₂) with ha
  set b : ℝ := (R₀ + r₂) / (R₀ - r₂) with hb
  have ha0 : 0 ≤ a := by rw [ha, hR₀, hr₂]; norm_num
  have hb0 : 0 ≤ b := by rw [hb, hR₀, hr₂]; norm_num
  set c1 : ℝ := 1 / Real.log 2 with hc1
  have hc10 : 0 ≤ c1 := by rw [hc1]; positivity
  refine ⟨a * (lc * c1 + K) + b * E * c1 + E, by positivity, U₀, hU₀2, fun U hU u hu1 hUq hUq2 hu g hg hgL t ht => ?_⟩
  have hU2 : 2 ≤ U := le_trans hU₀2 hU
  have hUpos : 0 < U := by linarith
  have hsub := hdisk U hU t ht
  refine ⟨hsub, ?_⟩
  set c : ℂ := (2 : ℂ) + (t : ℂ) * Complex.I with hcdef
  have hcre : c.re = 2 := by simp [hcdef]
  have hre : ∀ s : ℂ, ‖s - c‖ ≤ 1 → |s.re - 2| ≤ ‖s - c‖ := by
    intro s _
    have h1 : (s - c).re = s.re - 2 := by simp [hcdef]
    rw [← h1]
    exact Complex.abs_re_le_norm _
  have hre' : ∀ s : ℂ, ‖s - c‖ ≤ ‖s - c‖ → |s.re - 2| ≤ ‖s - c‖ := by
    intro s _
    have h1 : (s - c).re = s.re - 2 := by simp [hcdef]
    rw [← h1]
    exact Complex.abs_re_le_norm _
  have hgan : AnalyticOnNhd ℂ g (Metric.ball c R₀) := fun z _ => hg.analyticAt z

  have hnz : ∀ s ∈ Metric.ball c R₀, g s ≠ 0 := by
    intro s hs h0
    have hs' := hsub hs
    have hs0 : 0 < s.re := by
      have := hs'.1
      unfold σ₀ at this
      linarith
    have hlz : IsLZero (D.omega u) s :=
      ⟨hs0, g, fun z _ => hg.analyticAt z, hgL, h0⟩
    exact hu (mem_exceptionalSet_of_zero D ρ U u hu1 hUq hUq2 s hlz hs'.1.le hs'.2.le)
  obtain ⟨hEan, hEexp, hEbd⟩ := hEf (D.omega u)
  have hc1' : 1 < c.re := by rw [hcre]; norm_num
  have hcexp : Complex.exp (eulerLog (D.omega u) c) = g c := by
    rw [hgL c hc1']
    exact hEexp c hc1'
  obtain ⟨ℓ, hℓan, hℓexp, hℓc⟩ :=
    exists_analytic_log_ball hgan hnz hcexp (by rw [hR₀]; norm_num)
  have hEc : ‖eulerLog (D.omega u) c‖ ≤ E := by
    apply hEbd
    rw [hcre]; norm_num
  refine ⟨ℓ, hℓan, hℓexp, hℓc, ?_, ?_⟩
  ·
    have hlogU : Real.log 2 ≤ Real.log U := Real.log_le_log (by norm_num) hU2
    have hM : ∀ s ∈ Metric.ball c R₀, (ℓ s).re ≤ lc + K * Real.log U := by
      intro s hs
      have hs' := hsub hs
      have hsn : ‖s - c‖ < R₀ := by
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hs
      have h1 := hre' s le_rfl
      have hsre := abs_lt.mp (lt_of_le_of_lt h1 hsn)
      have hUρ : (1 : ℝ) ≤ U ^ ρ := Real.one_le_rpow (by linarith) hρ.1.le
      have hb := hconv' u hu1 U hU2 hUq hUq2 g hg hgL s
        (by rw [hR₀] at hsre; linarith [hsre.1]) (by rw [hR₀] at hsre; linarith [hsre.2])
        (by linarith [hs'.2])
      have hnorm : ‖g s‖ = Real.exp (ℓ s).re := by
        rw [hℓexp s hs, Complex.norm_exp]
      have hpos : 0 < C₁ * U ^ K := by positivity
      have hle : (ℓ s).re ≤ Real.log (C₁ * U ^ K) := by
        rw [Real.le_log_iff_exp_le hpos, ← hnorm]; exact hb
      rw [Real.log_mul hC₁.ne' (by positivity), Real.log_rpow hUpos] at hle
      have : Real.log C₁ ≤ lc := le_abs_self _
      linarith
    have hM0 : 0 ≤ lc + K * Real.log U := by
      have : 0 ≤ Real.log U := le_trans hlog2.le hlogU
      positivity
    have hBC := borel_caratheodory (c := c) (r := r₂) (R := R₀) (by rw [hr₂]; norm_num)
      (by rw [hr₂, hR₀]; norm_num) hM0 hℓan hM
    intro s hs
    refine le_trans (hBC s hs) ?_
    rw [hℓc]
    have hL1 : 1 ≤ c1 * Real.log U := by
      rw [hc1, one_div, inv_mul_eq_div, le_div_iff₀ hlog2]; linarith
    have h1 : a * lc * 1 ≤ a * lc * (c1 * Real.log U) :=
      mul_le_mul_of_nonneg_left hL1 (by positivity)
    have h2 : b * E * 1 ≤ b * E * (c1 * Real.log U) :=
      mul_le_mul_of_nonneg_left hL1 (by positivity)
    have h3 : 0 ≤ E * Real.log U := by
      have : 0 ≤ Real.log U := le_trans hlog2.le hlogU
      positivity
    have h4 : b * ‖eulerLog (D.omega u) c‖ ≤ b * E := mul_le_mul_of_nonneg_left hEc hb0
    nlinarith
  ·
    have hsub1 : Metric.ball c 1 ⊆ Metric.ball c R₀ :=
      Metric.ball_subset_ball (by rw [hR₀]; norm_num)
    have hEan' : AnalyticOnNhd ℂ (eulerLog (D.omega u)) (Metric.ball c 1) := by
      refine AnalyticOnNhd.mono hEan ?_
      intro s hs
      have hsn : ‖s - c‖ < 1 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hs
      have h1 := hre' s le_rfl
      have := abs_lt.mp (lt_of_le_of_lt h1 hsn)
      show 1 < s.re
      linarith [this.1]
    have huniq := analytic_log_unique_ball (c := c) (R := 1) (ℓ₁ := ℓ)
      (ℓ₂ := eulerLog (D.omega u)) one_pos (hℓan.mono hsub1) hEan'
      (fun s hs => by
        have hs1 : 1 < s.re := by
          have hsn : ‖s - c‖ < 1 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hs
          have h1 := hre' s le_rfl
          have := abs_lt.mp (lt_of_le_of_lt h1 hsn)
          linarith [this.1]
        rw [← hℓexp s (hsub1 hs), hgL s hs1]
        exact (hEexp s hs1).symm) hℓc
    intro s hs
    have hs1 : s ∈ Metric.ball c 1 :=
      Metric.closedBall_subset_ball (by rw [hr₀]; norm_num) hs
    rw [huniq s hs1]
    have hpos : 0 ≤ a * (lc * c1 + K) + b * E * c1 := by positivity
    refine le_trans (hEbd s ?_) (by linarith)
    have hsn : ‖s - c‖ ≤ r₀ := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hs
    have h1 := hre' s le_rfl
    have := abs_le.mp (le_trans h1 hsn)
    rw [hr₀] at this
    linarith [this.1]

end

end DedekindZetaZeroFree.Quantitative.ReciprocalLogDisk
