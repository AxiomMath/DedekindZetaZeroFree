module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem finite_ideals_absNorm_le (F : Type*) [Field F] [NumberField F] (X : ℝ) :
    {I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ X}.Finite := by
  rcases lt_or_ge X 0 with hX | hX
  · refine Set.finite_empty.subset ?_
    rintro I hI
    exact absurd (le_trans (Nat.cast_nonneg (Ideal.absNorm I)) hI) (not_le.mpr hX)
  · refine (Ideal.finite_setOfPred_absNorm_le ⌊X⌋₊).subset ?_
    rintro I hI
    exact (Nat.le_floor_iff hX).mpr hI

noncomputable def boundedNormIdeals (F : Type*) [Field F] [NumberField F] (X : ℝ) :
    Finset (Ideal (𝓞 F)) :=
  (finite_ideals_absNorm_le F X).toFinset

@[simp]
theorem mem_boundedNormIdeals {F : Type*} [Field F] [NumberField F]
    {X : ℝ} {I : Ideal (𝓞 F)} :
    I ∈ boundedNormIdeals F X ↔ (Ideal.absNorm I : ℝ) ≤ X := by
  rw [boundedNormIdeals, Set.Finite.mem_toFinset]
  rfl

theorem boundedNormIdeals_mono (F : Type*) [Field F] [NumberField F]
    {X Y : ℝ} (hXY : X ≤ Y) :
    boundedNormIdeals F X ⊆ boundedNormIdeals F Y := by
  intro I hI
  rw [mem_boundedNormIdeals] at hI ⊢
  exact le_trans hI hXY

@[simp]
theorem boundedNormIdeals_eq_empty_of_neg (F : Type*) [Field F] [NumberField F]
    {X : ℝ} (hX : X < 0) : boundedNormIdeals F X = ∅ := by
  ext I
  simp only [mem_boundedNormIdeals, Finset.notMem_empty, iff_false, not_le]
  exact lt_of_lt_of_le hX (Nat.cast_nonneg (Ideal.absNorm I))

@[simp]
theorem boundedNormIdeals_eq_singleton_bot (F : Type*) [Field F] [NumberField F]
    {X : ℝ} (hX0 : 0 ≤ X) (hX1 : X < 1) : boundedNormIdeals F X = {⊥} := by
  ext I
  rw [mem_boundedNormIdeals, Finset.mem_singleton]
  constructor
  · intro hI
    have h0 : Ideal.absNorm I = 0 := by
      by_contra h
      have h1 : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      linarith
    exact Ideal.absNorm_eq_zero_iff.mp h0
  · rintro rfl
    simpa using hX0

@[simp]
theorem boundedNormIdeals_one (F : Type*) [Field F] [NumberField F] :
    boundedNormIdeals F 1 = {⊥, ⊤} := by
  ext I
  rw [mem_boundedNormIdeals, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hI
    have h1 : Ideal.absNorm I ≤ 1 := by exact_mod_cast hI
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h | h
    · exact Or.inl (Ideal.absNorm_eq_zero_iff.mp h)
    · exact Or.inr (Ideal.absNorm_eq_one_iff.mp h)
  · rintro (rfl | rfl) <;> simp

end DedekindZetaZeroFree.LargeSieve
