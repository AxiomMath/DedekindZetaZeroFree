module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Hadamard
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

namespace DedekindZetaZeroFree.Quantitative.ThreeCircles

open Complex Set Metric
open Complex.HadamardThreeLines

theorem three_circles (ℓ : ℂ → ℂ) (c : ℂ) (R r₀ r₁ r₂ : ℝ) (hr₀ : 0 < r₀) (hr₀₂ : r₀ < r₂)
    (hr₁₂ : r₁ ≤ r₂) (hr₂ : r₂ < R)
    (hℓ : DifferentiableOn ℂ ℓ (Metric.ball c R)) (A L : ℝ) (hA : 0 < A) (hL : 1 ≤ L)
    (hsmall : ∀ s ∈ closedBall c r₀, ‖ℓ s‖ ≤ A)
    (hbig : ∀ s ∈ closedBall c r₂, ‖ℓ s‖ ≤ A * L)
    (w : ℝ) (hw0 : r₀ < |w|) (hw : |w| ≤ r₁) :
    ‖ℓ (c + w)‖ ≤ A * L ^ ((Real.log r₁ - Real.log r₀) / (Real.log r₂ - Real.log r₀)) := by
  have hlu : Real.log r₀ < Real.log r₂ := Real.log_lt_log hr₀ hr₀₂
  have hsub : 0 < Real.log r₂ - Real.log r₀ := by linarith
  have hexp_le : ∀ z : ℂ, z.re ≤ Real.log r₂ → ‖Complex.exp z‖ ≤ r₂ := by
    intro z hz
    rw [Complex.norm_exp]
    calc Real.exp z.re ≤ Real.exp (Real.log r₂) := Real.exp_le_exp.mpr hz
      _ = r₂ := Real.exp_log (by linarith)
  have hmem : ∀ z : ℂ, z.re ≤ Real.log r₂ → c + Complex.exp z ∈ closedBall c r₂ := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hexp_le z hz
  let f : ℂ → ℂ := fun z => ℓ (c + Complex.exp z)
  have hd : DiffContOnCl ℂ f (verticalStrip (Real.log r₀) (Real.log r₂)) := by
    apply DifferentiableOn.diffContOnCl
    have hcl : closure (verticalStrip (Real.log r₀) (Real.log r₂)) =
        verticalClosedStrip (Real.log r₀) (Real.log r₂) := by
      rw [verticalStrip, verticalClosedStrip, Complex.closure_preimage_re, closure_Ioo hlu.ne]
    rw [hcl]
    intro z hz
    have hz2 : z.re ≤ Real.log r₂ := hz.2
    have h1 : c + Complex.exp z ∈ Metric.ball c R := by
      have := hmem z hz2
      rw [mem_closedBall] at this
      rw [mem_ball]; linarith
    have h2 : DifferentiableAt ℂ (fun z => c + Complex.exp z) z := by fun_prop
    exact (DifferentiableAt.comp z (hℓ.differentiableAt (isOpen_ball.mem_nhds h1)) h2
      ).differentiableWithinAt
  have hB : BddAbove ((norm ∘ f) '' verticalClosedStrip (Real.log r₀) (Real.log r₂)) := by
    refine ⟨A * L, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hbig _ (hmem z hz.2)
  have ha : ∀ z ∈ re ⁻¹' {Real.log r₀}, ‖f z‖ ≤ A := by
    intro z hz
    have hz' : z.re = Real.log r₀ := hz
    show ‖ℓ (c + Complex.exp z)‖ ≤ A
    apply hsmall
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp, hz',
      Real.exp_log hr₀]
  have hb : ∀ z ∈ re ⁻¹' {Real.log r₂}, ‖f z‖ ≤ A * L := by
    intro z hz
    have hz' : z.re = Real.log r₂ := hz
    exact hbig _ (hmem z hz'.le)
  have hw0' : (w : ℂ) ≠ 0 := by
    intro h
    have : w = 0 := by exact_mod_cast h
    rw [this] at hw0
    simp at hw0
    linarith
  have hre : (Complex.log (w : ℂ)).re = Real.log |w| := by
    rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs]
  have hr₁pos : 0 < |w| := by linarith
  have hlog1 : Real.log |w| ≤ Real.log r₁ := Real.log_le_log hr₁pos hw
  have hlog2 : Real.log r₁ ≤ Real.log r₂ :=
    Real.log_le_log (by linarith) hr₁₂
  have hlog0 : Real.log r₀ ≤ Real.log |w| := Real.log_le_log hr₀ hw0.le
  have hz0 : Complex.log (w : ℂ) ∈ verticalClosedStrip (Real.log r₀) (Real.log r₂) := by
    show (Complex.log (w : ℂ)).re ∈ Icc (Real.log r₀) (Real.log r₂)
    rw [hre]
    exact ⟨hlog0, hlog1.trans hlog2⟩
  have key := norm_le_interp_of_mem_verticalClosedStrip' (f := f) (z := Complex.log (w : ℂ))
    (a := A) (b := A * L) hlu hz0 hd hB ha hb
  have hfz : f (Complex.log (w : ℂ)) = ℓ (c + w) := by
    show ℓ (c + Complex.exp (Complex.log (w : ℂ))) = ℓ (c + w)
    rw [Complex.exp_log hw0']
  rw [hfz, hre] at key
  have hx0 : 0 ≤ (Real.log |w| - Real.log r₀) / (Real.log r₂ - Real.log r₀) :=
    div_nonneg (by linarith) hsub.le
  have hx1 : (Real.log |w| - Real.log r₀) / (Real.log r₂ - Real.log r₀) ≤
      (Real.log r₁ - Real.log r₀) / (Real.log r₂ - Real.log r₀) :=
    div_le_div_of_nonneg_right (by linarith) hsub.le
  have hL0 : 0 ≤ L := by linarith
  have heq : ∀ x : ℝ, A ^ (1 - x) * (A * L) ^ x = A * L ^ x := by
    intro x
    rw [Real.mul_rpow hA.le hL0, ← mul_assoc, ← Real.rpow_add hA]
    simp
  refine key.trans ?_
  rw [heq]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hx1) hA.le

theorem absorb (C θ ε : ℝ) (hC : 0 < C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → C * x ^ θ ≤ ε * x + K := by
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (C / ε) ^ (1 / (1 - θ)) := ⟨_, rfl⟩
  have hXpos : 0 < X := by rw [hX]; exact Real.rpow_pos_of_pos (div_pos hC hε) _
  have hXθ : X ^ (1 - θ) = C / ε := by
    rw [hX, ← Real.rpow_mul (div_pos hC hε).le, one_div, inv_mul_cancel₀ (by linarith),
      Real.rpow_one]
  refine ⟨C * X, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hεx : 0 ≤ ε * x := by positivity
  by_cases hxX : x ≤ X
  · have h1 : x ^ θ ≤ x := by
      calc x ^ θ ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx hθ1.le
        _ = x := Real.rpow_one x
    have h2 := mul_le_mul_of_nonneg_left h1 hC.le
    have h3 := mul_le_mul_of_nonneg_left hxX hC.le
    linarith
  · push_neg at hxX
    have h2 : X ^ (1 - θ) ≤ x ^ (1 - θ) := Real.rpow_le_rpow hXpos.le hxX.le (by linarith)
    have h3 : x ^ (1 - θ) * x ^ θ = x := by
      rw [← Real.rpow_add hx0]; simp
    rw [hXθ, div_le_iff₀ hε] at h2
    have h4 : C ≤ ε * x ^ (1 - θ) := by rw [mul_comm]; exact h2
    have h5 : C * x ^ θ ≤ ε * x ^ (1 - θ) * x ^ θ :=
      mul_le_mul_of_nonneg_right h4 (by positivity)
    have h6 : 0 ≤ C * X := by positivity
    calc C * x ^ θ ≤ ε * x ^ (1 - θ) * x ^ θ := h5
      _ = ε * x := by rw [mul_assoc, h3]
      _ ≤ ε * x + C * X := by linarith

end DedekindZetaZeroFree.Quantitative.ThreeCircles
