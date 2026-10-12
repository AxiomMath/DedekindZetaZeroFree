module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.DivisorRectangleEnvelopes

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.DivisorBins
variable {F : Type} [Field F] [NumberField F]

def divisorBin (P : ℝ) : Finset (Ideal (𝓞 F)) :=
  (boundedNormIdeals F (2 * P)).filter (ErrorRectangles.InBin P)

theorem bin_exists (X : ℝ) (hX : 1 ≤ 2 * X) (f : Ideal (𝓞 F))
    (hf0 : f ≠ ⊥) (hf : norm f ≤ 2 * X) :
    ∃ P ∈ ErrorRectangles.scales X, 1 ≤ P ∧ P ≤ 2 * X ∧ ErrorRectangles.InBin P f := by
  have hfn : 1 ≤ norm f := by
    unfold norm
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hf0)
  have hXX : 2 * X ≤ 2 * max 1 X := by gcongr; exact le_max_right _ _
  have hcover : ∃ j : ℕ, norm f ≤ (2 : ℝ) ^ j :=
    ⟨Vendor.dyadicLength (2 * max 1 X), hf.trans (hXX.trans (Vendor.dyadicLength_cover _))⟩
  let j := Nat.find hcover
  have hj : norm f ≤ (2 : ℝ) ^ j := Nat.find_spec hcover
  have hjle : j ≤ Vendor.dyadicLength (2 * max 1 X) :=
    Nat.find_min' hcover (hf.trans (hXX.trans (Vendor.dyadicLength_cover _)))
  rcases hj0 : j with _ | k
  · refine ⟨1, by simp [ErrorRectangles.scales], le_rfl, hX, hf0, ?_, ?_⟩
    · simpa using hfn
    · have hh : norm f ≤ 1 := by simpa [hj0] using hj
      linarith
  · have hk : k < Vendor.dyadicLength (2 * max 1 X) := by omega
    have hlow : (2 : ℝ) ^ k < norm f := by
      exact lt_of_not_ge (Nat.find_min hcover (by omega))
    refine ⟨(2 : ℝ) ^ k, ?_, one_le_pow₀ (by norm_num), hlow.le.trans hf, hf0, ?_, ?_⟩
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
    · split_ifs <;> linarith
    · simpa [hj0, pow_succ'] using hj

theorem bin_unique {X P R : ℝ} {f : Ideal (𝓞 F)}
    (hP : P ∈ ErrorRectangles.scales X) (hR : R ∈ ErrorRectangles.scales X)
    (hp : ErrorRectangles.InBin P f) (hr : ErrorRectangles.InBin R f) : P = R := by
  have power {S : ℝ} (hS : S ∈ ErrorRectangles.scales X) : ∃ i : ℕ, S = 2 ^ i := by
    rcases Finset.mem_insert.mp hS with h | h
    · exact ⟨0, by simpa using h⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact ⟨i, hi.symm⟩
  obtain ⟨i, rfl⟩ := power hP
  obtain ⟨j, rfl⟩ := power hR
  have step {i j : ℕ} (hij : i < j) : 2 * (2 : ℝ) ^ i ≤ (2 : ℝ) ^ j := by
    calc
      _ = (2 : ℝ) ^ (i+1) := by rw [pow_succ'];
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hij
  have nonone {j : ℕ} (hj : 0 < j) : (2 : ℝ) ^ j ≠ 1 := by
    have hh : (2 : ℝ) ≤ 2 ^ j := by
      simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj)
    linarith
  rcases lt_trichotomy i j with hij | hij | hij
  · have hj := nonone (by omega : 0 < j)
    have hl : (2 : ℝ) ^ j < norm f := by simpa [hj] using hr.2.1
    have hh := step hij
    linarith [hp.2.2]
  · rw [hij]
  · have hi := nonone (by omega : 0 < i)
    have hl : (2 : ℝ) ^ i < norm f := by simpa [hi] using hp.2.1
    have hh := step hij
    linarith [hr.2.2]

theorem sum_bin (u : Ideal (𝓞 F)) (hu : u ≠ ⊥) (P : ℝ) (H : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ idealDivisors u, if ErrorRectangles.InBin P a then H a else 0) =
      ∑ a ∈ divisorBin (F := F) P, if a ∣ u then H a else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_congr _ (by intros; rfl)
  ext a
  simp only [Finset.mem_filter, mem_idealDivisors hu, divisorBin,
    mem_boundedNormIdeals]
  constructor
  · rintro ⟨had, hbin⟩
    exact ⟨⟨hbin.2.2, hbin⟩, had⟩
  · rintro ⟨⟨_, hbin⟩, had⟩
    exact ⟨had, hbin⟩

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.DivisorBins

end
