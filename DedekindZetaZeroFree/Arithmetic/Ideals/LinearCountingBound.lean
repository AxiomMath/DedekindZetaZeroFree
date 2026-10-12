module

public import DedekindZetaZeroFree.Arithmetic.Ideals.BoundedNormFinsets

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

private theorem card_boundedNormIdeals_eq_natCard (F : Type*) [Field F] [NumberField F] (X : ℝ) :
    Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ X} = (boundedNormIdeals F X).card := by
  change Nat.card (setOf (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ) ≤ X)) =
    (boundedNormIdeals F X).card
  have h := Set.ncard_eq_toFinset_card
    (setOf (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ) ≤ X)) (finite_ideals_absNorm_le F X)
  rw [Nat.card_coe_set_eq, h]
  rfl

theorem exists_ideal_count_bound_finset (F : Type*) [Field F] [NumberField F] :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ X : ℝ, 1 ≤ X → ((boundedNormIdeals F X).card : ℝ) ≤ C * X) ∧
      (∀ X : ℝ, 1 ≤ X → ∀ s : Finset (Ideal (𝓞 F)),
        (∀ I ∈ s, (Ideal.absNorm I : ℝ) ≤ X) → (s.card : ℝ) ≤ C * X) := by
  classical

  have htend := NumberField.Ideal.tendsto_norm_le_div_atTop F
  obtain ⟨b, hb⟩ := (htend.isBoundedUnder_le (u := fun X : ℝ =>
    (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ X} : ℝ) / X)).eventually_le
  rw [Filter.eventually_atTop] at hb
  obtain ⟨T, hT⟩ := hb

  set T' : ℝ := max T 1 with hT'def
  have hT'1 : 1 ≤ T' := le_max_right _ _
  have hTT' : T ≤ T' := le_max_left _ _
  have hbound : ∀ X : ℝ, T' ≤ X → ((boundedNormIdeals F X).card : ℝ) ≤ b * X := by
    intro X hX
    have hX1 : 1 ≤ X := le_trans hT'1 hX
    have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
    have h := hT X (le_trans hTT' hX)
    rw [card_boundedNormIdeals_eq_natCard F X] at h
    exact (div_le_iff₀ hXpos).mp h

  set K : ℝ := max 1 (max b ((boundedNormIdeals F T').card : ℝ)) with hK
  have hK1 : 1 ≤ K := by rw [hK]; exact le_max_left _ _
  have hglob : ∀ X : ℝ, 1 ≤ X → ((boundedNormIdeals F X).card : ℝ) ≤ K * X := by
    intro X hX1
    have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
    rcases le_or_gt T' X with h | h
    · have hb' := hbound X h
      have hKb : b ≤ K := by
        rw [hK]; exact le_trans (le_max_left _ _) (le_max_right _ _)
      exact le_trans hb' (mul_le_mul_of_nonneg_right hKb (le_of_lt hXpos))
    · have hmono : boundedNormIdeals F X ⊆ boundedNormIdeals F T' :=
        boundedNormIdeals_mono F (le_of_lt h)
      have hcard : ((boundedNormIdeals F X).card : ℝ) ≤ ((boundedNormIdeals F T').card : ℝ) := by
        exact_mod_cast Finset.card_le_card hmono
      have hKT : ((boundedNormIdeals F T').card : ℝ) ≤ K := by
        rw [hK]; exact le_trans (le_max_right _ _) (le_max_right _ _)
      exact le_trans hcard (le_trans hKT (le_mul_of_one_le_right (le_trans zero_le_one hK1) hX1))
  refine ⟨K, hK1, hglob, ?_⟩
  intro X hX1 s hs
  have hsub : s ⊆ boundedNormIdeals F X := by
    intro I hI
    rw [mem_boundedNormIdeals]
    exact hs I hI
  have hcard : (s.card : ℝ) ≤ ((boundedNormIdeals F X).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact le_trans hcard (hglob X hX1)

theorem exists_ideal_count_bound (F : Type*) [Field F] [NumberField F] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      ((boundedNormIdeals F X).card : ℝ) ≤ C * X := by
  obtain ⟨C, hC, hglobal, _⟩ := exists_ideal_count_bound_finset F
  exact ⟨C, hC, hglobal⟩

end DedekindZetaZeroFree.LargeSieve
