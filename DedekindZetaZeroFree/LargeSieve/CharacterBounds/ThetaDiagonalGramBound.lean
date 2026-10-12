module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.SmoothThetaAndGramKernels
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.CharacterValues
public import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

theorem initial_theta_diagonal (F : Type) [Field F] [NumberField F] :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ M : ℝ, 1 ≤ M → ∀ v : Ideal (𝓞 F) → ℂ, (∀ I, ‖v I‖ ≤ 1) →
        ‖initialTheta F (fun I => v I * (starRingEnd ℂ) (v I)) M‖ ≤ D * M := by
  obtain ⟨C, hC, hcount⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound F
  refine ⟨(5 / 2) * C, mul_nonneg (by norm_num) (by linarith), ?_⟩
  intro M hM v hv
  have hX : (1 : ℝ) ≤ (5 / 2) * M := by linarith
  have hweight : ∀ t : ℝ, ‖((DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight t : ℂ))‖ ≤ 1 := by
    intro t
    have h : ‖((DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight t : ℂ))‖ = DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight t :=
      RCLike.norm_of_nonneg (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_nonneg t)
    rw [h]
    exact DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_le_one t
  have hterm : ∀ I : Ideal (𝓞 F),
      ‖((DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight ((Ideal.absNorm I : ℝ) / M) : ℂ)) *
        (v I * (starRingEnd ℂ) (v I))‖ ≤ 1 := by
    intro I
    have hv1 : ‖v I * (starRingEnd ℂ) (v I)‖ ≤ 1 := by
      rw [norm_mul, starRingEnd_apply, Complex.star_def, Complex.norm_conj]
      exact mul_le_one₀ (hv I) (norm_nonneg _) (hv I)
    rw [norm_mul]
    exact mul_le_one₀ (hweight _) (norm_nonneg _) hv1
  have h1 : ‖initialTheta F (fun I => v I * (starRingEnd ℂ) (v I)) M‖ ≤
      (((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M)).filter (fun I => I ≠ ⊥)).card : ℝ) := by
    rw [initialTheta]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ I ∈ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M)).filter (fun I => I ≠ ⊥),
            ‖((DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight ((Ideal.absNorm I : ℝ) / M) : ℂ)) *
              (v I * (starRingEnd ℂ) (v I))‖
        ≤ ∑ _I ∈ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M)).filter (fun I => I ≠ ⊥),
            (1 : ℝ) := Finset.sum_le_sum fun I _ => hterm I
      _ = (((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M)).filter (fun I => I ≠ ⊥)).card : ℝ) := by
          simp
  have h2 : (((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M)).filter (fun I => I ≠ ⊥)).card : ℝ) ≤
      (5 / 2) * C * M := by
    have hcast : (((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M)).filter
          (fun I => I ≠ ⊥)).card : ℝ) ≤
        ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M)).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le _ _
    calc (((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M)).filter (fun I => I ≠ ⊥)).card : ℝ)
        ≤ ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M)).card : ℝ) := hcast
      _ ≤ C * ((5 / 2) * M) := hcount ((5 / 2) * M) hX
      _ = (5 / 2) * C * M := by ring
  linarith

theorem initialGram_diagonal_bound (F : Type) [Field F] [NumberField F] :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c),
        ∀ M : ℝ, 1 ≤ M → ∀ b : Ideal (𝓞 F), Squarefree b → b ⊔ c = ⊤ →
          ‖initialGram F Q M b b‖ ≤ D * M := by
  obtain ⟨D, hD, hbound⟩ := initial_theta_diagonal F
  refine ⟨D, hD, ?_⟩
  intro c Q M hM b hb hbc
  exact hbound M hM (fun I => (Q.χ b) I)
    (fun I => DedekindZetaZeroFree.LargeSieve.quadraticFamily_norm_le_one Q hb hbc I)

end DedekindZetaZeroFree.LargeSieve.Sieve
