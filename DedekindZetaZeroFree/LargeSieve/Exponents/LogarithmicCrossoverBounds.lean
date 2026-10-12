module

public import DedekindZetaZeroFree.LargeSieve.Exponents.ExponentAndRecursiveEnvelope

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/SelectedExponents.lean.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonComparison.lean.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/LogarithmicLoss.lean.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

namespace DedekindZetaZeroFree.LargeSieve

theorem crossover_identity (α M N : ℝ) (hα : 1 ≤ α) (hα₂ : α ≤ 2)
    (hM : 1 ≤ M) (hN : 1 ≤ N) :
    N ^ (2 * α - 1) * (N ^ (2 - 1 / α)) ^ (1 - α) = N ^ (2 - 1 / α) := by
  have hα0 : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
  have hβ : 2 * α - 1 + (2 - 1 / α) * (1 - α) = 2 - 1 / α := by
    field_simp; ring
  rw [hβ]

end DedekindZetaZeroFree.LargeSieve
