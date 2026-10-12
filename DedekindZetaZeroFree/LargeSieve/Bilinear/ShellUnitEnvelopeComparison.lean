module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.GcdTailAndMaskedShellBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.LargeSieve.Sieve.CoreCoefficient
open scoped NumberField Classical

private lemma weight_bound (W : ℝ → ℝ) (hW : SieveWeight W) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, W t ≤ B := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (1 / 2 : ℝ) ≤ 5 / 2))
    hW.smooth.continuous.continuousOn
  refine ⟨W x, hW.nonneg x, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (1 / 2 : ℝ) (5 / 2)
  · exact hmax ht
  · rw [hW.zero_outside t ht]
    exact hW.nonneg x

theorem unit_column_bound
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (hW : SieveWeight W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M K : ℝ, 1 ≤ M → B2unitColumn F c Q W M K ≤ C * M := by
  obtain ⟨A, hA1, hA⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound F
  obtain ⟨B, hB0, hB⟩ := weight_bound W hW
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  refine ⟨B * A * (5 / 2), by positivity, ?_⟩
  intro M K hM
  have hchi : ∀ a : Ideal (𝓞 F), ‖(Q.χ ⊤) a‖ ≤ 1 := by
    intro a
    exact quadraticFamily_norm_le_one Q (by simpa using (squarefree_one : Squarefree (1 : Ideal (𝓞 F)))) (by simp) a
  have hcard : ((kernelRows F c M K).card : ℝ) ≤ A * ((5 / 2) * M) := by
    calc _ ≤ ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M)).card : ℝ) := by
          exact_mod_cast Finset.card_filter_le (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M)) _
      _ ≤ A * ((5 / 2) * M) := hA _ (by linarith)
  calc B2unitColumn F c Q W M K
      ≤ ∑ a ∈ kernelRows F c M K, B := by
        apply Finset.sum_le_sum
        intro a ha
        have hc : ‖(Q.χ ⊤) a‖ ^ 2 ≤ 1 := by
          nlinarith [hchi a, norm_nonneg ((Q.χ ⊤) a)]
        exact (mul_le_of_le_one_right (hW.nonneg _) hc).trans (hB _)
    _ = ((kernelRows F c M K).card : ℝ) * B := by simp [mul_comm]
    _ ≤ (A * ((5 / 2) * M)) * B := mul_le_mul_of_nonneg_right hcard hB0
    _ = B * A * (5 / 2) * M := by ring

theorem envelope_comparison
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (hW : SieveWeight W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M X Y K : ℝ,
      1 ≤ M → 0 < X → 1 ≤ Y → X ≤ Y → 0 < K →
      B2env F c Q W M X K ≤ B2env F c Q W M Y K + C * M := by
  obtain ⟨C, hC0, hC⟩ := unit_column_bound F c Q W hW
  obtain ⟨A, hA1, hA⟩ := B2_trivial_bound F W hW
  refine ⟨C, hC0, ?_⟩
  intro M X Y K hM hX hY hXY hK
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hY0 : 0 ≤ B2env F c Q W M Y K := by
    unfold B2env
    exact Real.sSup_nonneg' ⟨0, Or.inl (Or.inl rfl), le_rfl⟩
  let SY : Set ℝ := {0} ∪
    {x : ℝ | ∃ T : ℝ, 1 ≤ T ∧ T ≤ Y ∧ x = B2 F c Q W M T K} ∪
    {x : ℝ | Y < 1 ∧ 1 ≤ 2 * Y ∧ x = B2unitColumn F c Q W M K}
  have hbdd : BddAbove SY := by
    refine ⟨A * M * Y, ?_⟩
    rintro z ((hz | ⟨T, hT1, hTY, rfl⟩) | ⟨hYlt, -⟩)
    · have hz0 : z = 0 := hz
      rw [hz0]
      positivity
    · exact (hA c Q M T K hM hT1 hK).trans
        (mul_le_mul_of_nonneg_left hTY (by positivity))
    · exact absurd hYlt (not_lt.mpr hY)
  apply csSup_le
  · exact ⟨0, Or.inl (Or.inl rfl)⟩
  · rintro z ((hz | ⟨T, hT1, hTX, rfl⟩) | ⟨hXlt, hX2, rfl⟩)
    · have hz0 : z = 0 := hz
      rw [hz0]
      exact add_nonneg hY0 (mul_nonneg hC0 hM0)
    · have ht : B2 F c Q W M T K ≤ B2env F c Q W M Y K := by
        apply le_csSup hbdd
        exact Or.inl (Or.inr ⟨T, hT1, hTX.trans hXY, rfl⟩)
      exact ht.trans (le_add_of_nonneg_right (mul_nonneg hC0 hM0))
    · exact (hC M K hM).trans (le_add_of_nonneg_left hY0)

end DedekindZetaZeroFree.LargeSieve.Sieve.CoreCoefficient

end
