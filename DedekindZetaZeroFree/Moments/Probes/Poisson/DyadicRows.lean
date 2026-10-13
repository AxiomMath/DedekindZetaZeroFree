module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyData
public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyCount

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawRowSumDefinitions31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def q (u : Frequency D.recipe) : ℝ := frequencyNorm D.recipe u

def dyadIndex (u : Frequency D.recipe) : ℕ := Nat.log 2 ⌊q D u⌋₊

theorem one_le_q (u : Frequency D.recipe) : (1 : ℝ) ≤ q D u :=
  RawFrequencyCount.one_le_frequencyNorm D.recipe u

theorem dyadIndex_spec (u : Frequency D.recipe) :
    (2 : ℝ) ^ dyadIndex D u ≤ q D u ∧ q D u < (2 : ℝ) ^ (dyadIndex D u + 1) := by
  have h1 := one_le_q D u
  have hn : ⌊q D u⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊q D u⌋₊ := Nat.le_floor (by simpa using h1)
    omega
  constructor
  · have h := Nat.pow_log_le_self 2 hn
    have h2 : ((2 ^ Nat.log 2 ⌊q D u⌋₊ : ℕ) : ℝ) ≤ (⌊q D u⌋₊ : ℝ) := by exact_mod_cast h
    have h3 : (⌊q D u⌋₊ : ℝ) ≤ q D u := Nat.floor_le (by linarith)
    unfold dyadIndex
    push_cast at h2
    linarith
  · have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) ⌊q D u⌋₊
    have h2 : ((⌊q D u⌋₊ : ℕ) : ℝ) < ((2 ^ (Nat.log 2 ⌊q D u⌋₊ + 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    have h3 : q D u < (⌊q D u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h4 : (⌊q D u⌋₊ : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 ⌊q D u⌋₊ + 1) : ℕ) : ℝ) := by
      have : ⌊q D u⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊q D u⌋₊ + 1) := h
      exact_mod_cast this
    unfold dyadIndex
    push_cast at h4
    linarith

theorem dyadIndex_spec' (u : Frequency D.recipe) :
    (2 : ℝ) ^ dyadIndex D u ≤ q D u ∧ q D u < 2 * (2 : ℝ) ^ dyadIndex D u := by
  have h := dyadIndex_spec D u
  rw [pow_succ] at h
  exact ⟨h.1, by linarith [h.2]⟩

theorem dyadIndex_eq_of_bounds (u : Frequency D.recipe) (k : ℕ)
    (h1 : (2 : ℝ) ^ k ≤ q D u) (h2 : q D u < (2 : ℝ) ^ (k + 1)) : dyadIndex D u = k := by
  have a1 : 2 ^ k ≤ ⌊q D u⌋₊ := by
    apply Nat.le_floor
    exact_mod_cast h1
  have a2 : ⌊q D u⌋₊ < 2 ^ (k + 1) := by
    apply Nat.floor_lt (by linarith [one_le_q D u]) |>.mpr
    exact_mod_cast h2
  exact Nat.log_eq_of_pow_le_of_lt_pow a1 a2

theorem dyadIndex_unique (u : Frequency D.recipe) (k : ℕ) :
    dyadIndex D u = k ↔ (2 : ℝ) ^ k ≤ q D u ∧ q D u < (2 : ℝ) ^ (k + 1) := by
  constructor
  · rintro rfl
    exact dyadIndex_spec D u
  · exact fun h => dyadIndex_eq_of_bounds D u k h.1 h.2

def rawDyad (k : ℕ) : Set (Frequency D.recipe) := {u | dyadIndex D u = k}

theorem rawDyad_eq (k : ℕ) :
    rawDyad D k = {u : Frequency D.recipe | (2 : ℝ) ^ k ≤ frequencyNorm D.recipe u ∧
      frequencyNorm D.recipe u < 2 * (2 : ℝ) ^ k} := by
  ext u
  simp only [rawDyad, Set.mem_setOf_eq, dyadIndex_unique, pow_succ]
  change _ ≤ q D u ∧ q D u < _ ↔ _ ≤ q D u ∧ q D u < _
  constructor <;> rintro ⟨a, b⟩ <;> exact ⟨a, by linarith⟩

theorem mem_rawDyad_self (u : Frequency D.recipe) : u ∈ rawDyad D (dyadIndex D u) := rfl

theorem rawDyad_disjoint {k l : ℕ} (h : k ≠ l) : Disjoint (rawDyad D k) (rawDyad D l) := by
  rw [Set.disjoint_left]
  intro u hk hl
  exact h (hk.symm.trans hl)

theorem iUnion_rawDyad : (⋃ k, rawDyad D k) = Set.univ := by
  ext u
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨_, mem_rawDyad_self D u⟩

theorem rawDyad_finite_card :
    ∃ K : ℝ, 0 < K ∧ ∀ k : ℕ, (rawDyad D k).Finite ∧
      (Set.ncard (rawDyad D k) : ℝ) ≤ K * (2 : ℝ) ^ k := by
  obtain ⟨K, hK, h⟩ := RawFrequencyCount.frequency_dyad_count D.recipe
  refine ⟨K, hK, fun k => ?_⟩
  rw [rawDyad_eq]
  exact h _ (one_le_pow₀ (by norm_num))

theorem dyadIndex_principal : dyadIndex D (principalFrequency D.recipe) = 0 := by
  have h : q D (principalFrequency D.recipe) = 1 :=
    RawFrequencyCount.frequencyNorm_principal D.recipe
  unfold dyadIndex
  rw [h]
  simp

theorem rawDyad_zero_nonempty : (rawDyad D 0).Nonempty :=
  ⟨principalFrequency D.recipe, dyadIndex_principal D⟩

theorem q_principal : q D (principalFrequency D.recipe) = 1 :=
  RawFrequencyCount.frequencyNorm_principal D.recipe

theorem finite_q_le (B : ℝ) : {u : Frequency D.recipe | q D u ≤ B}.Finite := by
  obtain ⟨K, hK, h⟩ := RawFrequencyCount.frequency_count_lt D.recipe
  refine ((h (max 1 (B + 1)) (le_max_left _ _)).1).subset ?_
  intro u hu
  have : q D u ≤ B := hu
  change frequencyNorm D.recipe u < _
  exact lt_of_lt_of_le (by change q D u < B + 1; linarith) (le_max_right _ _)

def smallSet (Z : ℝ) : Set (Frequency D.recipe) :=
  {u | u ≠ principalFrequency D.recipe ∧ q D u ≤ Z ^ Scales.smallCutoffExponent}

def mediumSet (Z : ℝ) : Set (Frequency D.recipe) :=
  {u | u ≠ principalFrequency D.recipe ∧ Z ^ Scales.smallCutoffExponent < q D u ∧ q D u ≤ Z ^ Scales.largeCutoffExponent}

def largeSet (Z : ℝ) : Set (Frequency D.recipe) :=
  {u | u ≠ principalFrequency D.recipe ∧ Z ^ Scales.largeCutoffExponent < q D u}

theorem smallSet_finite (Z : ℝ) : (smallSet D Z).Finite :=
  (finite_q_le D (Z ^ Scales.smallCutoffExponent)).subset fun _ h => h.2

theorem mediumSet_finite (Z : ℝ) : (mediumSet D Z).Finite :=
  (finite_q_le D (Z ^ Scales.largeCutoffExponent)).subset fun _ h => h.2.2

theorem nonprincipal_cover (Z : ℝ) :
    {u : Frequency D.recipe | u ≠ principalFrequency D.recipe} =
      smallSet D Z ∪ mediumSet D Z ∪ largeSet D Z := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_union, smallSet, mediumSet, largeSet]
  constructor
  · intro h
    by_cases h1 : q D u ≤ Z ^ Scales.smallCutoffExponent
    · exact Or.inl (Or.inl ⟨h, h1⟩)
    · by_cases h2 : q D u ≤ Z ^ Scales.largeCutoffExponent
      · exact Or.inl (Or.inr ⟨h, not_le.mp h1, h2⟩)
      · exact Or.inr ⟨h, not_le.mp h2⟩
  · rintro ((h | h) | h)
    · exact h.1
    · exact h.1
    · exact h.1

theorem small_medium_disjoint (Z : ℝ) : Disjoint (smallSet D Z) (mediumSet D Z) := by
  rw [Set.disjoint_left]
  intro u h1 h2
  exact absurd h1.2 (not_le.mpr h2.2.1)

theorem small_large_disjoint (Z : ℝ) (hZ : 1 ≤ Z) : Disjoint (smallSet D Z) (largeSet D Z) := by
  rw [Set.disjoint_left]
  intro u h1 h2
  have : Z ^ Scales.smallCutoffExponent ≤ Z ^ Scales.largeCutoffExponent :=
    Real.rpow_le_rpow_of_exponent_le hZ (by unfold Scales.smallCutoffExponent Scales.largeCutoffExponent; norm_num)
  linarith [h1.2, h2.2]

theorem medium_large_disjoint (Z : ℝ) : Disjoint (mediumSet D Z) (largeSet D Z) := by
  rw [Set.disjoint_left]
  intro u h1 h2
  exact absurd h1.2.2 (not_le.mpr h2.2)

theorem mem_small_iff (Z : ℝ) (u : Frequency D.recipe) :
    u ∈ smallSet D Z ↔ u ≠ principalFrequency D.recipe ∧ q D u ≤ Z ^ Scales.smallCutoffExponent := Iff.rfl

theorem mem_medium_iff (Z : ℝ) (u : Frequency D.recipe) :
    u ∈ mediumSet D Z ↔
      u ≠ principalFrequency D.recipe ∧ Z ^ Scales.smallCutoffExponent < q D u ∧ q D u ≤ Z ^ Scales.largeCutoffExponent := Iff.rfl

theorem mem_large_iff (Z : ℝ) (u : Frequency D.recipe) :
    u ∈ largeSet D Z ↔ u ≠ principalFrequency D.recipe ∧ Z ^ Scales.largeCutoffExponent < q D u := Iff.rfl

def exceptionalMedium (ρ Z : ℝ) : Set (Frequency D.recipe) :=
  {u | u ∈ mediumSet D Z ∧ u ∈ RawFixed.FixedData.rawExceptionalSet D ρ ((2 : ℝ) ^ dyadIndex D u)}

def goodMedium (ρ Z : ℝ) : Set (Frequency D.recipe) :=
  {u | u ∈ mediumSet D Z ∧ u ∉ RawFixed.FixedData.rawExceptionalSet D ρ ((2 : ℝ) ^ dyadIndex D u)}

theorem exceptionalMedium_subset (ρ Z : ℝ) : exceptionalMedium D ρ Z ⊆ mediumSet D Z :=
  fun _ h => h.1

theorem goodMedium_subset (ρ Z : ℝ) : goodMedium D ρ Z ⊆ mediumSet D Z :=
  fun _ h => h.1

theorem exceptional_good_disjoint (ρ Z : ℝ) :
    Disjoint (exceptionalMedium D ρ Z) (goodMedium D ρ Z) := by
  rw [Set.disjoint_left]
  intro u h1 h2
  exact h2.2 h1.2

theorem exceptional_good_union (ρ Z : ℝ) :
    exceptionalMedium D ρ Z ∪ goodMedium D ρ Z = mediumSet D Z := by
  ext u
  simp only [exceptionalMedium, goodMedium, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    by_cases h' : u ∈ RawFixed.FixedData.rawExceptionalSet D ρ ((2 : ℝ) ^ dyadIndex D u)
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, h'⟩

theorem exceptionalMedium_finite (ρ Z : ℝ) : (exceptionalMedium D ρ Z).Finite :=
  (mediumSet_finite D Z).subset (exceptionalMedium_subset D ρ Z)

theorem goodMedium_finite (ρ Z : ℝ) : (goodMedium D ρ Z).Finite :=
  (mediumSet_finite D Z).subset (goodMedium_subset D ρ Z)

theorem exceptionalMedium_mem_dyad {ρ Z : ℝ} {u : Frequency D.recipe}
    (h : u ∈ exceptionalMedium D ρ Z) :
    u ∈ RawFixed.FixedData.rawExceptionalSet D ρ ((2 : ℝ) ^ dyadIndex D u) ∧
      u ∈ rawDyad D (dyadIndex D u) := ⟨h.2, rfl⟩

def dyadPiece (a b : ℝ) (k : ℕ) : Set (Frequency D.recipe) :=
  {u | u ≠ principalFrequency D.recipe ∧ a < q D u ∧ q D u ≤ b ∧ dyadIndex D u = k}

theorem dyadPiece_subset_rawDyad (a b : ℝ) (k : ℕ) : dyadPiece D a b k ⊆ rawDyad D k :=
  fun _ h => h.2.2.2

theorem dyadPiece_finite (a b : ℝ) (k : ℕ) : (dyadPiece D a b k).Finite :=
  (finite_q_le D b).subset fun _ h => h.2.2.1

theorem dyadPiece_card_le (a b : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ k : ℕ,
      (Set.ncard (dyadPiece D a b k) : ℝ) ≤ K * (2 : ℝ) ^ k := by
  obtain ⟨K, hK, h⟩ := rawDyad_finite_card D
  refine ⟨K, hK, fun k => le_trans ?_ (h k).2⟩
  exact Nat.cast_le.mpr (Set.ncard_le_ncard (dyadPiece_subset_rawDyad D a b k) (h k).1)

theorem dyadPiece_disjoint (a b : ℝ) {k l : ℕ} (h : k ≠ l) :
    Disjoint (dyadPiece D a b k) (dyadPiece D a b l) :=
  (rawDyad_disjoint D h).mono (dyadPiece_subset_rawDyad D a b k)
    (dyadPiece_subset_rawDyad D a b l)

theorem dyadPiece_empty_of_large (a b : ℝ) {k : ℕ} (hk : b < (2 : ℝ) ^ k) :
    dyadPiece D a b k = ∅ := by
  ext u
  simp only [dyadPiece, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, -, h2, h3⟩
  have := (dyadIndex_spec D u).1
  rw [h3] at this
  linarith

theorem iUnion_dyadPiece (a b : ℝ) :
    (⋃ k, dyadPiece D a b k) =
      {u : Frequency D.recipe | u ≠ principalFrequency D.recipe ∧ a < q D u ∧ q D u ≤ b} := by
  ext u
  simp only [Set.mem_iUnion, dyadPiece, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, h1, h2, h3, -⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨dyadIndex D u, h1, h2, h3, rfl⟩

theorem mediumSet_eq_iUnion (Z : ℝ) :
    mediumSet D Z = ⋃ k, dyadPiece D (Z ^ Scales.smallCutoffExponent) (Z ^ Scales.largeCutoffExponent) k := by
  rw [iUnion_dyadPiece]
  rfl

theorem smallSet_eq_iUnion (Z : ℝ) :
    smallSet D Z = ⋃ k, dyadPiece D 0 (Z ^ Scales.smallCutoffExponent) k := by
  rw [iUnion_dyadPiece]
  ext u
  simp only [smallSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith [one_le_q D u], h2⟩
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩

end

end DedekindZetaZeroFree.Quantitative.RawRowSumDefinitions31
