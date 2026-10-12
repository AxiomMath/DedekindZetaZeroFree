module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

open scoped Topology

namespace DedekindZetaZeroFree

theorem mellin_arbitrary_epsilon_convergent
    (g : ℝ → ℂ) (σ : ℝ)
    (hlocal : MeasureTheory.LocallyIntegrableOn g (Set.Ioi 0))
    (htop : ∀ ε : ℝ, 0 < ε →
      g =O[Filter.atTop] (fun x : ℝ => x ^ (σ + ε)))
    (hzero : ∀ b : ℝ,
      g =O[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => x ^ b)) :
    ∀ s : ℂ, σ < s.re → MellinConvergent g (-s) := by
  intro s hs
  have hε : 0 < (s.re - σ) / 2 := by linarith
  refine mellinConvergent_of_isBigO_rpow (a := -(σ + (s.re - σ) / 2))
    (b := -(s.re + 1)) hlocal ?_ ?_ ?_ ?_
  · simpa using htop ((s.re - σ) / 2) hε
  · simp only [Complex.neg_re]
    linarith
  · simpa using hzero (s.re + 1)
  · simp only [Complex.neg_re]
    linarith

theorem mellin_arbitrary_epsilon_holomorphic
    (g : ℝ → ℂ) (σ : ℝ)
    (hlocal : MeasureTheory.LocallyIntegrableOn g (Set.Ioi 0))
    (htop : ∀ ε : ℝ, 0 < ε →
      g =O[Filter.atTop] (fun x : ℝ => x ^ (σ + ε)))
    (hzero : ∀ b : ℝ,
      g =O[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => x ^ b)) :
    AnalyticOnNhd ℂ (fun s : ℂ => mellin g (-s)) {s : ℂ | σ < s.re} := by
  rw [Complex.analyticOnNhd_iff_differentiableOn
    (isOpen_lt continuous_const Complex.continuous_re)]
  intro s hs
  have hs' : σ < s.re := hs
  have hε : 0 < (s.re - σ) / 2 := by linarith
  have hdiff : DifferentiableAt ℂ (mellin g) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (a := -(σ + (s.re - σ) / 2))
      (b := -(s.re + 1)) hlocal ?_ ?_ ?_ ?_
  · exact (hdiff.comp s differentiable_neg.differentiableAt).differentiableWithinAt.mono
      (Set.subset_univ _)
  · simpa using htop ((s.re - σ) / 2) hε
  · simp only [Complex.neg_re]
    linarith
  · simpa using hzero (s.re + 1)
  · simp only [Complex.neg_re]
    linarith

end DedekindZetaZeroFree
