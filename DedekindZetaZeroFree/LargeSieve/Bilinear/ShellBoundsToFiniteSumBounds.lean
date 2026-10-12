module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.GlobalEstimatesFromShells
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.FiniteSupportQuadraticForms

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

private lemma card_boundedNormIdeals_eq_natCard (F : Type*) [Field F] [NumberField F] (X : ℝ) :
    (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card =
      Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ X} := by
  have hset : ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X) : Set (Ideal (𝓞 F))) =
      {I | (Ideal.absNorm I : ℝ) ≤ X} := by
    ext I; exact DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals
  rw [(Set.ncard_coe_finset (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X)).symm, hset]
  exact (Nat.card_coe_set_eq ({I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ X})).symm

private lemma exists_ideal_count_bound (F : Type*) [Field F] [NumberField F] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) ≤ C * X := by
  classical
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp
    (NumberField.Ideal.tendsto_norm_le_div_atTop F)) 1 zero_lt_one
  have hbound : ∀ᶠ X : ℝ in Filter.atTop,
      (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ X} : ℝ) / X ≤
        (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ N₀} : ℝ) / N₀ + 2 := by
    filter_upwards [Filter.eventually_ge_atTop N₀] with X hX
    have h1 := hN₀ X hX
    have h2 := hN₀ N₀ le_rfl
    rw [Real.dist_eq] at h1 h2
    linarith [abs_lt.mp h1, abs_lt.mp h2]
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hbound
  set T' : ℝ := max T 1 with hT'
  set B : ℝ := (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ N₀} : ℝ) / N₀ + 2
    with hB
  set C : ℝ := max 1 (max B ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F T').card : ℝ)) with hC
  have hC1 : 1 ≤ C := by rw [hC]; exact le_max_left _ _
  refine ⟨C, hC1, ?_⟩
  intro X hX
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  by_cases hTX : T' ≤ X
  · have hcard := card_boundedNormIdeals_eq_natCard F X
    have hf : (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ X} : ℝ) ≤ B * X := by
      have hh := hT X (le_trans (le_max_left T 1) hTX)
      rw [hB] at hh ⊢
      rw [div_le_iff₀ (by linarith : (0:ℝ) < X)] at hh
      linarith [hh]
    have h2 : ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) ≤ B * X := by
      rw [hcard]; exact hf
    refine le_trans h2 ?_
    rw [hC]
    exact mul_le_mul_of_nonneg_right
      (le_trans (le_max_left B ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F T').card : ℝ))
        (le_max_right (1:ℝ) (max B ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F T').card : ℝ))))
      (by linarith : (0:ℝ) ≤ X)
  · have hXT : X < T' := not_le.mp hTX
    have hmono : (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card ≤ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F T').card :=
      Finset.card_le_card (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals_mono F (le_of_lt hXT))
    have hle : ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) ≤ C := by
      have h2 : ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) ≤
          ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F T').card : ℝ) := by exact_mod_cast hmono
      rw [hC]
      exact le_trans h2 (le_trans (le_max_right B ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F T').card : ℝ))
        (le_max_right (1:ℝ) (max B ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F T').card : ℝ))))
    nlinarith [hC0, hX, hle]

theorem shell_bound_to_target_finsum
    (F : Type) [Field F] [NumberField F]
    (𝔠 : Ideal (𝓞 F)) (𝓕 : DedekindZetaZeroFree.QuadraticHeckeFamily F 𝔠)
    (hShell : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N → ∀ lam : Ideal (𝓞 F) → ℂ,
        (∑ 𝔞 ∈ paperShell F 𝔠 M,
          ‖∑ 𝔟 ∈ paperShell F 𝔠 N, lam 𝔟 * (𝓕.χ 𝔟) 𝔞‖ ^ 2) ≤
            C * (M * N) ^ δ * (M + N) *
              ∑ 𝔟 ∈ paperShell F 𝔠 N, ‖lam 𝔟‖ ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (M N : ℝ) (lam : Ideal (𝓞 F) → ℂ), 1 ≤ M → 1 ≤ N →
        ∑ᶠ 𝔞 : Ideal (𝓞 F), (if Squarefree 𝔞 ∧ 𝔞 ⊔ 𝔠 = ⊤ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ M then
            ‖∑ᶠ 𝔟 : Ideal (𝓞 F), (if Squarefree 𝔟 ∧ 𝔟 ⊔ 𝔠 = ⊤ ∧ (Ideal.absNorm 𝔟 : ℝ) ≤ N then
              lam 𝔟 * (𝓕.χ 𝔟) 𝔞 else 0)‖ ^ 2 else 0) ≤
          D * (M * N) ^ ε * (M + N) *
            ∑ᶠ 𝔟 : Ideal (𝓞 F), (if Squarefree 𝔟 ∧ 𝔟 ⊔ 𝔠 = ⊤ ∧ (Ideal.absNorm 𝔟 : ℝ) ≤ N then
              ‖lam 𝔟‖ ^ 2 else 0) := by
  classical
  obtain ⟨A, hA1, hcount⟩ := exists_ideal_count_bound F
  intro ε hε
  obtain ⟨D, hD0, hD⟩ := global_from_shell_bounds F 𝔠 𝓕 A hA1 hcount hShell ε hε
  refine ⟨D, hD0, ?_⟩
  intro M N lam hM hN
  rw [finsum_energy_eq_sum, finsum_coeff_norm_sq_eq_sum]
  exact hD M N hM hN lam

end DedekindZetaZeroFree.LargeSieve.Sieve
