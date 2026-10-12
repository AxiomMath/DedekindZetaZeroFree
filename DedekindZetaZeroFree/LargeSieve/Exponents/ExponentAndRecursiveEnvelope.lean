module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonComparison.lean.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/LogarithmicLoss.lean.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

namespace DedekindZetaZeroFree.LargeSieve

def HasExponent (B : ℝ → ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      B M N ≤ C * (M * N) ^ ε * (M + N ^ α)

def HasRecursiveEnvelope (B : ℝ → ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      B M N ≤ C * (M * N) ^ ε *
        (M + N + N ^ (2 * α - 1) * M ^ (1 - α))

end DedekindZetaZeroFree.LargeSieve
