module

public import DedekindZetaZeroFree.LargeSieve.Exponents.ExponentAndRecursiveEnvelope
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.InitialQuadraticHeckeEstimate

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem exponent_initial
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (c : Ideal (𝓞 F)) (𝓕 : DedekindZetaZeroFree.QuadraticHeckeFamily F c) :
    HasExponent (Sieve.B1 F c 𝓕) 2 := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := Sieve.initialBound F hF c 𝓕 ε hε
  refine ⟨C + 1, by linarith, ?_⟩
  intro M N hM hN
  refine le_trans (hbound M N hM hN) ?_
  show C * Real.rpow (M * N) ε * (M + Real.rpow N 2) ≤
    (C + 1) * Real.rpow (M * N) ε * (M + Real.rpow N 2)
  have hX : (0 : ℝ) ≤ Real.rpow (M * N) ε := Real.rpow_nonneg (by positivity) ε
  have hY : (0 : ℝ) ≤ M + Real.rpow N 2 := by
    have : (0 : ℝ) ≤ Real.rpow N 2 := Real.rpow_nonneg (by linarith) 2
    linarith
  apply mul_le_mul_of_nonneg_right _ hY
  exact mul_le_mul_of_nonneg_right (by linarith) hX

end DedekindZetaZeroFree.LargeSieve
