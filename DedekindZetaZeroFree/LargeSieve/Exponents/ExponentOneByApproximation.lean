module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import DedekindZetaZeroFree.LargeSieve.Exponents.ExponentAndRecursiveEnvelope

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonComparison.lean.
-/

namespace DedekindZetaZeroFree.LargeSieve

theorem hasExponent_one_of_approximation (B : ℝ → ℝ → ℝ)
    (h : ∀ η : ℝ, 0 < η → ∃ α : ℝ, α ≤ 1 + η ∧ HasExponent B α) :
    HasExponent B 1 := by
  intro ε hε
  have hη : 0 < ε / 2 := by linarith
  obtain ⟨α, hα, hExp⟩ := h (ε / 2) hη
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hExp (ε / 2) hη
  refine ⟨2 * C₀, by linarith, ?_⟩
  intro M N hM hN
  rw [Real.rpow_one]
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hMNpos : 0 < M * N := mul_pos hMpos hNpos
  have hMN1 : 1 ≤ M * N := by nlinarith
  have hhalf : 0 ≤ ε / 2 := le_of_lt hη
  have hp : 0 < (M * N) ^ (ε / 2) := Real.rpow_pos_of_pos hMNpos _

  have hNα : N ^ α ≤ N * (M * N) ^ (ε / 2) := by
    have h1 : N ^ α ≤ N ^ (1 + ε / 2) := Real.rpow_le_rpow_of_exponent_le hN hα
    have h2 : N ^ (1 + ε / 2) = N * N ^ (ε / 2) := by
      rw [Real.rpow_add hNpos, Real.rpow_one]
    have hNM : N ≤ M * N := by nlinarith
    have h3 : N ^ (ε / 2) ≤ (M * N) ^ (ε / 2) :=
      Real.rpow_le_rpow (le_of_lt hNpos) hNM hhalf
    rw [h2] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left h3 (le_of_lt hNpos))

  have hMle : M ≤ (M + N) * (M * N) ^ (ε / 2) := by
    have h1 : 1 ≤ (M * N) ^ (ε / 2) := Real.one_le_rpow hMN1 hhalf
    have h2 : 0 ≤ M + N := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have hsum : M + N ^ α ≤ 2 * (M + N) * (M * N) ^ (ε / 2) := by
    have hNM' : N ≤ M + N := by linarith
    nlinarith [hMle, hNα, le_of_lt hp, hNM']
  calc B M N ≤ C₀ * (M * N) ^ (ε / 2) * (M + N ^ α) := hC₀ M N hM hN
    _ ≤ C₀ * (M * N) ^ (ε / 2) * (2 * (M + N) * (M * N) ^ (ε / 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * C₀ * (M * N) ^ ε * (M + N) := by
        have hrw : (M * N) ^ ε = (M * N) ^ (ε / 2) * (M * N) ^ (ε / 2) := by
          conv_lhs => rw [show ε = ε / 2 + ε / 2 by ring]
          rw [Real.rpow_add hMNpos]
        rw [hrw]; ring

end DedekindZetaZeroFree.LargeSieve
