module

public import DedekindZetaZeroFree.LargeSieve.Exponents.QuadraticHeckeExponentOne
public import DedekindZetaZeroFree.LargeSieve.Bilinear.ShellBoundsToFiniteSumBounds

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem goldmakherLouvel :
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyComplex F →
  ∀ (𝔠 : Ideal (𝓞 F)) (𝓕 : DedekindZetaZeroFree.QuadraticHeckeFamily F 𝔠) (ε : ℝ), 0 < ε →
    ∃ C : ℝ, ∀ (M N : ℝ) (lam : Ideal (𝓞 F) → ℂ), 1 ≤ M → 1 ≤ N →
      ∑ᶠ 𝔞 : Ideal (𝓞 F), (if Squarefree 𝔞 ∧ 𝔞 ⊔ 𝔠 = ⊤ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ M then
          ‖∑ᶠ 𝔟 : Ideal (𝓞 F), (if Squarefree 𝔟 ∧ 𝔟 ⊔ 𝔠 = ⊤ ∧ (Ideal.absNorm 𝔟 : ℝ) ≤ N then
            lam 𝔟 * (𝓕.χ 𝔟) 𝔞 else 0)‖ ^ 2 else 0) ≤
        C * (M * N) ^ ε * (M + N) *
          ∑ᶠ 𝔟 : Ideal (𝓞 F), (if Squarefree 𝔟 ∧ 𝔟 ⊔ 𝔠 = ⊤ ∧ (Ideal.absNorm 𝔟 : ℝ) ≤ N then
            ‖lam 𝔟‖ ^ 2 else 0) := by
  intro F _ _ hF 𝔠 𝓕 ε hε
  have hShell : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N → ∀ lam : Ideal (𝓞 F) → ℂ,
        (∑ 𝔞 ∈ Sieve.paperShell F 𝔠 M,
          ‖∑ 𝔟 ∈ Sieve.paperShell F 𝔠 N, lam 𝔟 * (𝓕.χ 𝔟) 𝔞‖ ^ 2) ≤
            C * (M * N) ^ δ * (M + N) *
              ∑ 𝔟 ∈ Sieve.paperShell F 𝔠 N, ‖lam 𝔟‖ ^ 2 := by
    intro δ hδ
    obtain ⟨C, hC, hCb⟩ := Sieve.hasSieveExponent_one F hF 𝔠 𝓕 δ hδ
    refine ⟨C, hC, ?_⟩
    intro M N hM hN lam
    have hB1 : Sieve.B1 F 𝔠 𝓕 M N ≤ C * (M * N) ^ δ * (M + N) := by
      have h := hCb M N hM hN
      simpa [Real.rpow_one] using h
    have hQ := Sieve.Q1_le_B1_mul_energy 𝓕 M N lam
    have henergy : 0 ≤ Sieve.energy F 𝔠 N lam := by
      simp only [Sieve.energy]
      exact Finset.sum_nonneg fun b _ => by positivity
    calc
      (∑ 𝔞 ∈ Sieve.paperShell F 𝔠 M,
          ‖∑ 𝔟 ∈ Sieve.paperShell F 𝔠 N, lam 𝔟 * (𝓕.χ 𝔟) 𝔞‖ ^ 2)
          = Sieve.Q1 F 𝔠 𝓕 M N lam := by
            simp only [Sieve.Q1, Sieve.rowSum]
      _ ≤ Sieve.B1 F 𝔠 𝓕 M N * Sieve.energy F 𝔠 N lam := hQ
      _ ≤ (C * (M * N) ^ δ * (M + N)) * Sieve.energy F 𝔠 N lam :=
            mul_le_mul_of_nonneg_right hB1 henergy
      _ = C * (M * N) ^ δ * (M + N) * Sieve.energy F 𝔠 N lam := by ring
  obtain ⟨D, _hD, hD⟩ := Sieve.shell_bound_to_target_finsum F 𝔠 𝓕 hShell ε hε
  exact ⟨D, hD⟩

end DedekindZetaZeroFree.LargeSieve
