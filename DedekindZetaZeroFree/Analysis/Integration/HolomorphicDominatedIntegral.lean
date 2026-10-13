module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative

open MeasureTheory Metric Set Filter Topology

namespace HolomorphicDominatedIntegral

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem hasDerivAt_integral_of_locally_dominated
    {U : Set ℂ} (hU : IsOpen U) {G : ℂ → α → E}
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (G z) μ)
    (hdiff : ∀ p, DifferentiableOn ℂ (fun z => G z p) U)
    (hdom : ∀ z0 ∈ U, ∃ r > 0, Metric.ball z0 r ⊆ U ∧
      ∃ g : α → ℝ, Integrable g μ ∧ ∀ z ∈ Metric.ball z0 r, ∀ p, ‖G z p‖ ≤ g p)
    {z0 : ℂ} (hz0 : z0 ∈ U) :
    Integrable (fun p => deriv (fun z => G z p) z0) μ ∧
      HasDerivAt (fun z => ∫ p, G z p ∂μ) (∫ p, deriv (fun z => G z p) z0 ∂μ) z0 := by
  obtain ⟨r, hr, hrU, g, hg, hbd⟩ := hdom z0 hz0
  have hr2 : 0 < r / 2 := by positivity
  have hsub : Metric.ball z0 (r / 2) ⊆ Metric.ball z0 r := ball_subset_ball (by linarith)
  have hdiffAt : ∀ p, ∀ z ∈ U, DifferentiableAt ℂ (fun z => G z p) z :=
    fun p z hz => (hdiff p z hz).differentiableAt (hU.mem_nhds hz)

  have hder_bd : ∀ p, ∀ z ∈ Metric.ball z0 (r / 2), ‖deriv (fun z => G z p) z‖ ≤ g p / (r / 2) := by
    intro p z hz
    have hcl : closedBall z (r / 2) ⊆ Metric.ball z0 r := by
      intro w hw
      rw [mem_ball] at hz ⊢
      rw [mem_closedBall] at hw
      have := dist_triangle w z z0
      linarith
    have hdc : DiffContOnCl ℂ (fun z => G z p) (Metric.ball z (r / 2)) :=
      DifferentiableOn.diffContOnCl
        ((hdiff p).mono ((closure_ball_subset_closedBall.trans hcl).trans hrU))
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr2 hdc
      (fun w hw => hbd w (hcl (sphere_subset_closedBall hw)) p)
  have hFmeas : ∀ᶠ z in 𝓝 z0, AEStronglyMeasurable (G z) μ :=
    Filter.mem_of_superset (ball_mem_nhds z0 hr) (fun z hz => hmeas z (hrU hz))
  have hFint : Integrable (G z0) μ :=
    hg.mono' (hmeas z0 hz0) (Filter.Eventually.of_forall fun p =>
      hbd z0 (mem_ball_self hr) p)

  have hF'meas : AEStronglyMeasurable (fun p => deriv (fun z => G z p) z0) μ := by
    let h : ℕ → ℂ := fun n => ((r / 4 / ((n : ℝ) + 1) : ℝ) : ℂ)
    have hh0 : ∀ n, h n ≠ 0 := by
      intro n
      have : (0 : ℝ) < r / 4 / ((n : ℝ) + 1) := by positivity
      exact Complex.ofReal_ne_zero.2 this.ne'
    have hhlim : Tendsto h atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall hh0⟩
      have : Tendsto (fun n : ℕ => r / 4 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat (r / 4) |>.comp (tendsto_add_atTop_nat 1) |>.congr
          (fun n => by simp [Function.comp])
      have := (Complex.continuous_ofReal.tendsto 0).comp this
      have h0 : (𝓝 (0 : ℂ)) = 𝓝 ((0 : ℝ) : ℂ) := by simp
      rw [h0]
      exact this
    have hmem : ∀ n, z0 + h n ∈ U := by
      intro n
      apply hrU
      rw [mem_ball, dist_eq_norm]
      have hn : (0 : ℝ) < r / 4 / ((n : ℝ) + 1) := by positivity
      have hle : r / 4 / ((n : ℝ) + 1) ≤ r / 4 := by
        apply div_le_self (by positivity)
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      simp only [h, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
      linarith
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := fun n p =>
      (h n)⁻¹ • (G (z0 + h n) p - G z0 p)) ?_ ?_
    · intro n
      exact ((hmeas _ (hmem n)).sub (hmeas z0 hz0)).const_smul _
    · refine Filter.Eventually.of_forall fun p => ?_
      have hd := (hdiffAt p z0 hz0).hasDerivAt
      have := hd.tendsto_slope_zero.comp hhlim
      refine this.congr fun n => ?_
      simp [Function.comp]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := G) (x₀ := z0) (s := Metric.ball z0 (r / 2)) (ball_mem_nhds z0 hr2) hFmeas hFint
    (F' := fun z p => deriv (fun z => G z p) z) hF'meas
    (bound := fun p => g p / (r / 2))
    (Filter.Eventually.of_forall fun p z hz => hder_bd p z hz)
    (hg.div_const _)
    (Filter.Eventually.of_forall fun p z hz =>
      (hdiffAt p z (hrU (hsub hz))).hasDerivAt)
  exact key

theorem differentiableOn_integral_of_locally_dominated
    {U : Set ℂ} (hU : IsOpen U) {G : ℂ → α → E}
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (G z) μ)
    (hdiff : ∀ p, DifferentiableOn ℂ (fun z => G z p) U)
    (hdom : ∀ z0 ∈ U, ∃ r > 0, Metric.ball z0 r ⊆ U ∧
      ∃ g : α → ℝ, Integrable g μ ∧ ∀ z ∈ Metric.ball z0 r, ∀ p, ‖G z p‖ ≤ g p) :
    DifferentiableOn ℂ (fun z => ∫ p, G z p ∂μ) U := fun z hz =>
  (hasDerivAt_integral_of_locally_dominated hU hmeas hdiff hdom hz).2.differentiableAt
    |>.differentiableWithinAt

theorem integrable_of_locally_dominated
    {U : Set ℂ} {G : ℂ → α → E}
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (G z) μ)
    (hdom : ∀ z0 ∈ U, ∃ r > 0, Metric.ball z0 r ⊆ U ∧
      ∃ g : α → ℝ, Integrable g μ ∧ ∀ z ∈ Metric.ball z0 r, ∀ p, ‖G z p‖ ≤ g p)
    {z : ℂ} (hz : z ∈ U) : Integrable (G z) μ := by
  obtain ⟨r, hr, -, g, hg, hbd⟩ := hdom z hz
  exact hg.mono' (hmeas z hz) (Filter.Eventually.of_forall fun p =>
    hbd z (mem_ball_self hr) p)

theorem differentiableOn_integral_prod_real
    {U : Set ℂ} (hU : IsOpen U) {G : ℂ → ℝ × ℝ → ℂ}
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (G z) (volume : Measure (ℝ × ℝ)))
    (hdiff : ∀ p, DifferentiableOn ℂ (fun z => G z p) U)
    (hdom : ∀ z0 ∈ U, ∃ r > 0, Metric.ball z0 r ⊆ U ∧
      ∃ g : ℝ × ℝ → ℝ, Integrable g (volume : Measure (ℝ × ℝ)) ∧
        ∀ z ∈ Metric.ball z0 r, ∀ p, ‖G z p‖ ≤ g p) :
    DifferentiableOn ℂ (fun z => ∫ p, G z p) U :=
  differentiableOn_integral_of_locally_dominated hU hmeas hdiff hdom

end HolomorphicDominatedIntegral

end DedekindZetaZeroFree.Quantitative
