module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleIdealRanges

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

theorem bot_not_mem_idealAdmissibleFinset (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (X : ℝ) :
    (⊥ : Ideal (𝓞 F)) ∉ idealAdmissibleFinset F c X := by
  rw [mem_idealAdmissibleFinset]
  rintro ⟨hsf, -⟩
  exact not_squarefree_zero (R := Ideal (𝓞 F)) (by simpa [Ideal.zero_eq_bot] using hsf)

theorem top_mem_idealAdmissibleFinset_iff (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (X : ℝ) :
    (⊤ : Ideal (𝓞 F)) ∈ idealAdmissibleFinset F c X ↔ 1 ≤ X := by
  rw [mem_idealAdmissibleFinset]
  constructor
  · rintro ⟨-, -, h⟩
    simpa using h
  · intro h
    exact ⟨by simpa [Ideal.one_eq_top] using squarefree_one (R := Ideal (𝓞 F)),
      top_sup_eq c, by simpa using h⟩

theorem one_le_absNorm_of_mem_idealAdmissibleFinset
    (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F)) (X : ℝ)
    (I : Ideal (𝓞 F)) (hI : I ∈ idealAdmissibleFinset F c X) :
    1 ≤ (Ideal.absNorm I : ℝ) := by
  rw [mem_idealAdmissibleFinset] at hI
  have hne : I ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using hI.1.ne_zero
  have hpos : 0 < Ideal.absNorm I :=
    Nat.pos_of_ne_zero fun h => hne (Ideal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast hpos

theorem idealAdmissibleFinset_eq_empty_of_lt_one
    (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F)) (X : ℝ)
    (hX : X < 1) : idealAdmissibleFinset F c X = ∅ := by
  ext I
  simp
  intro hI
  have h1 := one_le_absNorm_of_mem_idealAdmissibleFinset F c X I hI
  rw [mem_idealAdmissibleFinset] at hI
  linarith [hI.2.2]

theorem idealAdmissibleFinset_eq_singleton_of_one_le_of_lt_two
    (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F)) (X : ℝ)
    (hX : 1 ≤ X) (hX2 : X < 2) : idealAdmissibleFinset F c X = {⊤} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · rwa [top_mem_idealAdmissibleFinset_iff]
  · intro I hI
    have h1 := one_le_absNorm_of_mem_idealAdmissibleFinset F c X I hI
    rw [mem_idealAdmissibleFinset] at hI
    have h2 : (Ideal.absNorm I : ℝ) < 2 := lt_of_le_of_lt hI.2.2 hX2
    have h2n : Ideal.absNorm I < 2 := by exact_mod_cast h2
    have h1n : (1 : ℕ) ≤ Ideal.absNorm I := by exact_mod_cast h1
    have h5 : Ideal.absNorm I = 1 := by omega
    exact Ideal.absNorm_eq_one_iff.mp h5

theorem idealAdmissibleFinset_bot (F : Type) [Field F] [NumberField F] (X : ℝ) :
    idealAdmissibleFinset F ⊥ X = if 1 ≤ X then {⊤} else ∅ := by
  by_cases hX : 1 ≤ X
  · rw [if_pos hX]
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · rwa [top_mem_idealAdmissibleFinset_iff]
    · intro I hI
      rw [mem_idealAdmissibleFinset] at hI
      simpa using hI.2.1
  · rw [if_neg hX]
    ext I
    simp
    intro hI
    rw [mem_idealAdmissibleFinset] at hI
    have hItop : I = ⊤ := by simpa using hI.2.1
    rw [hItop] at hI
    exact hX (by simpa using hI.2.2)

theorem paperShell_bot_eq_empty (F : Type) [Field F] [NumberField F]
    (T : ℝ) (hT : 1 ≤ T) : paperShell F ⊥ T = ∅ := by
  rw [paperShell, idealAdmissibleFinset_bot, if_pos (by linarith : (1 : ℝ) ≤ 2 * T),
    Finset.filter_singleton]
  simp only [Ideal.absNorm_top, Nat.cast_one, if_neg (not_lt.mpr hT)]

end DedekindZetaZeroFree.LargeSieve.Sieve
