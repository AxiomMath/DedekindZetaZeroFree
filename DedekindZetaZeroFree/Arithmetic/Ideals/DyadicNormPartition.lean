module

public import DedekindZetaZeroFree.Arithmetic.Ideals.DyadicNormBlocks
public import DedekindZetaZeroFree.Analysis.DyadicLengthBounds

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

private lemma absNorm_le_two_pow_of_mem_idealDyadicBlock
    (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F))
    {j : ℕ} {I : Ideal (𝓞 F)} (h : I ∈ idealDyadicBlock F c j) :
    (Ideal.absNorm I : ℝ) ≤ (2 : ℝ) ^ j := by
  rcases j with _ | k
  · change I ∈ ({⊤} : Finset (Ideal (𝓞 F))) at h
    rw [Finset.mem_singleton] at h
    subst h
    simp
  · change I ∈ paperShell F c ((2 : ℝ) ^ k) at h
    obtain ⟨_, _, _, hup⟩ := (mem_paperShell F c ((2 : ℝ) ^ k) I).mp h
    rw [pow_succ']
    exact hup

private lemma absNorm_eq_one_of_mem_idealDyadicBlock_zero
    (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F))
    {I : Ideal (𝓞 F)} (h : I ∈ idealDyadicBlock F c 0) :
    Ideal.absNorm I = 1 := by
  change I ∈ ({⊤} : Finset (Ideal (𝓞 F))) at h
  rw [Finset.mem_singleton] at h
  subst h
  simp

private lemma two_pow_pred_lt_absNorm_of_mem_idealDyadicBlock
    (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F))
    {j : ℕ} (hj : j ≠ 0) {I : Ideal (𝓞 F)} (h : I ∈ idealDyadicBlock F c j) :
    (2 : ℝ) ^ (j - 1) < (Ideal.absNorm I : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  change I ∈ paperShell F c ((2 : ℝ) ^ k) at h
  obtain ⟨_, _, hlow, _⟩ := (mem_paperShell F c ((2 : ℝ) ^ k) I).mp h
  simpa using hlow

private lemma exists_dyadicBlock_of_mem_idealAdmissibleFinset
    (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F)) (X : ℝ) (hX : 1 ≤ X)
    {I : Ideal (𝓞 F)} (hI : I ∈ idealAdmissibleFinset F c X) :
    ∃ j ≤ DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength X, I ∈ idealDyadicBlock F c j := by
  obtain ⟨hsf, hcop, hnorm⟩ := (mem_idealAdmissibleFinset F c X I).mp hI
  have hne : I ≠ ⊥ := hsf.ne_zero
  have hnat : Ideal.absNorm I ≠ 0 := fun h => hne (Ideal.absNorm_eq_zero_iff.mp h)
  have hpos : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
    have : 1 ≤ Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr hnat
    exact_mod_cast this
  have hex : ∃ j : ℕ, (Ideal.absNorm I : ℝ) ≤ (2 : ℝ) ^ j :=
    ⟨DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength X,
      le_trans hnorm (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength_cover X)⟩
  have hmain : ∃ j : ℕ, (Ideal.absNorm I : ℝ) ≤ (2 : ℝ) ^ j ∧
      j ≤ DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength X ∧
      ∀ m < j, ¬ ((Ideal.absNorm I : ℝ) ≤ (2 : ℝ) ^ m) := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_, fun m hm => Nat.find_min hex hm⟩
    by_contra h
    exact Nat.find_min hex (Nat.lt_of_not_ge h)
      (le_trans hnorm (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength_cover X))
  obtain ⟨j, hspec, hjL, hjmin⟩ := hmain
  refine ⟨j, hjL, ?_⟩
  rcases j with _ | k
  · have hone : (Ideal.absNorm I : ℝ) = 1 := le_antisymm (by simpa using hspec) hpos
    have hnat1 : Ideal.absNorm I = 1 := by exact_mod_cast hone
    have htop : I = ⊤ := Ideal.absNorm_eq_one_iff.mp hnat1
    rw [htop]
    change (⊤ : Ideal (𝓞 F)) ∈ ({⊤} : Finset (Ideal (𝓞 F)))
    simp
  · have hlow : (2 : ℝ) ^ k < (Ideal.absNorm I : ℝ) :=
      lt_of_not_ge (hjmin k (Nat.lt_succ_self k))
    have hup : (Ideal.absNorm I : ℝ) ≤ 2 * (2 : ℝ) ^ k := by
      rw [pow_succ'] at hspec
      exact hspec
    change I ∈ paperShell F c ((2 : ℝ) ^ k)
    exact (mem_paperShell F c ((2 : ℝ) ^ k) I).mpr ⟨hsf, hcop, hlow, hup⟩

theorem biUnion_clippedDyadicBlock (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (X : ℝ) (hX : 1 ≤ X) :
    (Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength X + 1)).biUnion
      (clippedDyadicBlock F c X) = idealAdmissibleFinset F c X := by
  apply Finset.Subset.antisymm
  · intro I hI
    rw [Finset.mem_biUnion] at hI
    obtain ⟨j, _, hIj⟩ := hI
    simp only [clippedDyadicBlock, Finset.mem_inter] at hIj
    exact hIj.2
  · intro I hI
    obtain ⟨j, hjL, hblk⟩ := exists_dyadicBlock_of_mem_idealAdmissibleFinset F c X hX hI
    rw [Finset.mem_biUnion]
    refine ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjL), ?_⟩
    simp only [clippedDyadicBlock, Finset.mem_inter]
    exact ⟨hblk, hI⟩

theorem pairwiseDisjoint_clippedDyadicBlock (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (X : ℝ) (hX : 1 ≤ X) :
    Set.PairwiseDisjoint
      (↑(Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength X + 1)) : Set ℕ)
      (clippedDyadicBlock F c X) := by
  intro a _ b _ hab
  change Disjoint (clippedDyadicBlock F c X a) (clippedDyadicBlock F c X b)
  rw [Finset.disjoint_left]
  intro I hIa hIb
  simp only [clippedDyadicBlock, Finset.mem_inter] at hIa hIb
  obtain ⟨ha, _⟩ := hIa
  obtain ⟨hb, _⟩ := hIb
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · subst ha0
      have h1 : Ideal.absNorm I = 1 := absNorm_eq_one_of_mem_idealDyadicBlock_zero F c ha
      have hbne : b ≠ 0 := by omega
      have h2 := two_pow_pred_lt_absNorm_of_mem_idealDyadicBlock F c hbne hb
      rw [h1] at h2
      have h2' : (2 : ℝ) ^ (b - 1) < 1 := by simpa using h2
      have hge : (1 : ℝ) ≤ (2 : ℝ) ^ (b - 1) := one_le_pow₀ (by norm_num)
      linarith
    · have hle : (Ideal.absNorm I : ℝ) ≤ (2 : ℝ) ^ a :=
        absNorm_le_two_pow_of_mem_idealDyadicBlock F c ha
      have hbne : b ≠ 0 := by omega
      have h2 := two_pow_pred_lt_absNorm_of_mem_idealDyadicBlock F c hbne hb
      have hp : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ (b - 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
  · rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · subst hb0
      have h1 : Ideal.absNorm I = 1 := absNorm_eq_one_of_mem_idealDyadicBlock_zero F c hb
      have hane : a ≠ 0 := by omega
      have h2 := two_pow_pred_lt_absNorm_of_mem_idealDyadicBlock F c hane ha
      rw [h1] at h2
      have h2' : (2 : ℝ) ^ (a - 1) < 1 := by simpa using h2
      have hge : (1 : ℝ) ≤ (2 : ℝ) ^ (a - 1) := one_le_pow₀ (by norm_num)
      linarith
    · have hle : (Ideal.absNorm I : ℝ) ≤ (2 : ℝ) ^ b :=
        absNorm_le_two_pow_of_mem_idealDyadicBlock F c hb
      have hane : a ≠ 0 := by omega
      have h2 := two_pow_pred_lt_absNorm_of_mem_idealDyadicBlock F c hane ha
      have hp : (2 : ℝ) ^ b ≤ (2 : ℝ) ^ (a - 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      linarith

theorem dyadicScale_bounds (X : ℝ) (hX : 1 ≤ X) :
    ∀ j ∈ Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength X + 1),
      1 ≤ dyadicScale j ∧ dyadicScale j ≤ X := by
  intro j hj
  rw [Finset.mem_range] at hj
  rcases j with _ | k
  · refine ⟨le_refl 1, ?_⟩
    simpa [dyadicScale] using hX
  · have hk : k < DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength X := by omega
    have hlt : (2 : ℝ) ^ k < X := DedekindZetaZeroFree.LargeSieve.Vendor.pow_lt_of_lt_dyadicLength hX hk
    refine ⟨?_, le_of_lt hlt⟩
    show (1 : ℝ) ≤ (2 : ℝ) ^ k
    exact one_le_pow₀ (by norm_num)

theorem clippedDyadicBlock_subset_idealDyadicBlock
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (X : ℝ) (j : ℕ) :
    clippedDyadicBlock F c X j ⊆ idealDyadicBlock F c j := by
  intro I hI
  simp only [clippedDyadicBlock, Finset.mem_inter] at hI
  exact hI.1

end DedekindZetaZeroFree.LargeSieve.Sieve
