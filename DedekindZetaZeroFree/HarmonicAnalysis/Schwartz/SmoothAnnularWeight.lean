module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

/-
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/InitialBound.lean
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/InitialBound.lean.
Source: github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/InitialBound.lean.
-/

namespace DedekindZetaZeroFree.LargeSieve.Vendor

noncomputable section

open scoped NumberField Classical ContDiff

def annularWeightBump : ContDiffBump (3 / 2 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def annularWeight (t : ℝ) : ℝ := annularWeightBump t

@[simp] theorem annularWeightBump_rIn : annularWeightBump.rIn = (1 / 2 : ℝ) := rfl

@[simp] theorem annularWeightBump_rOut : annularWeightBump.rOut = (1 : ℝ) := rfl

theorem annularWeight_contDiff : ContDiff ℝ ∞ annularWeight := by
  exact annularWeightBump.contDiff

theorem annularWeight_hasCompactSupport : HasCompactSupport annularWeight := by
  exact annularWeightBump.hasCompactSupport

theorem annularWeight_nonneg (t : ℝ) : 0 ≤ annularWeight t := by
  exact annularWeightBump.nonneg' t

theorem annularWeight_le_one (t : ℝ) : annularWeight t ≤ 1 := by
  exact annularWeightBump.le_one (x := t)

theorem annularWeight_eq_one {t : ℝ} (h₁ : 1 ≤ t) (h₂ : t ≤ 2) :
    annularWeight t = 1 := by
  refine annularWeightBump.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq, abs_sub_le_iff, annularWeightBump_rIn]
  exact ⟨by linarith, by linarith⟩

theorem annularWeight_eq_zero_of_le {t : ℝ} (ht : t ≤ 1 / 2) :
    annularWeight t = 0 := by
  refine annularWeightBump.zero_of_le_dist ?_
  rw [Real.dist_eq, abs_of_nonpos (by linarith), annularWeightBump_rOut]
  linarith

theorem annularWeight_eq_zero_of_ge {t : ℝ} (ht : 5 / 2 ≤ t) :
    annularWeight t = 0 := by
  refine annularWeightBump.zero_of_le_dist ?_
  rw [Real.dist_eq, abs_of_nonneg (by linarith), annularWeightBump_rOut]
  linarith

end

end DedekindZetaZeroFree.LargeSieve.Vendor
