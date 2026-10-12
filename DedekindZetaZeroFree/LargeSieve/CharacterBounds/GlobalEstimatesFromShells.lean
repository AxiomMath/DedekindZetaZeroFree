module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.DyadicUnitBlockBounds
public import DedekindZetaZeroFree.Analysis.PartitionedQuadraticForms
public import DedekindZetaZeroFree.Analysis.QuadraticFormRestriction
public import DedekindZetaZeroFree.Arithmetic.Ideals.DyadicNormPartition

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

theorem global_from_shell_bounds
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (𝓕 : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (A : ℝ) (hA : 1 ≤ A)
    (hcount : ∀ X : ℝ, 1 ≤ X →
      ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) ≤ A * X)
    (hshell : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N → ∀ lam : Ideal (𝓞 F) → ℂ,
        (∑ a ∈ paperShell F c M,
          ‖∑ b ∈ paperShell F c N, lam b * (𝓕.χ b) a‖ ^ 2) ≤
        C * (M * N) ^ δ * (M + N) *
          ∑ b ∈ paperShell F c N, ‖lam b‖ ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N → ∀ lam : Ideal (𝓞 F) → ℂ,
        (∑ a ∈ idealAdmissibleFinset F c M,
          ‖∑ b ∈ idealAdmissibleFinset F c N, lam b * (𝓕.χ b) a‖ ^ 2) ≤
        D * (M * N) ^ ε * (M + N) *
          ∑ b ∈ idealAdmissibleFinset F c N, ‖lam b‖ ^ 2 := by
  intro ε hε
  have hη : 0 < ε / 2 := by linarith
  have hηle : 0 ≤ ε / 2 := hη.le
  obtain ⟨C, hC, hshellC⟩ := hshell (ε / 2) hη
  have hC' : 0 ≤ C + 2 * A + 1 := unit_block_extension_constant_nonneg C A hC hA
  set k : ℝ := 2 + 1 / ((ε / 2) * Real.log 2) with hkdef
  have hk : 0 < k := by rw [hkdef]; exact DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength_small_power_constant_pos hη
  refine ⟨(C + 2 * A + 1) * k ^ 2, mul_nonneg hC' (sq_nonneg k), ?_⟩
  intro M N hM hN lam
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hMN0 : 0 < M * N := mul_pos hM0 hN0
  have hub := unit_block_extension F c 𝓕 (ε / 2) hηle C hC A hA hcount hshellC
  have henergy_nn : 0 ≤ ∑ b ∈ idealAdmissibleFinset F c N, ‖lam b‖ ^ 2 :=
    Finset.sum_nonneg fun b _ => sq_nonneg _
  have hBbig_nn : 0 ≤ (C + 2 * A + 1) * ((M * N) ^ (ε / 2)) * (M + N) :=
    mul_nonneg (mul_nonneg hC' (Real.rpow_nonneg hMN0.le _)) (by linarith)
  have hblock : ∀ i ∈ Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength M + 1),
      ∀ j ∈ Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength N + 1),
      ∑ a ∈ clippedDyadicBlock F c M i,
        ‖∑ b ∈ clippedDyadicBlock F c N j, lam b * (𝓕.χ b) a‖ ^ 2 ≤
      ((C + 2 * A + 1) * ((M * N) ^ (ε / 2)) * (M + N)) *
        ∑ b ∈ clippedDyadicBlock F c N j, ‖lam b‖ ^ 2 := by
    intro i hi j hj
    obtain ⟨hmi1, hmiM⟩ := dyadicScale_bounds M hM i hi
    obtain ⟨hnj1, hnjN⟩ := dyadicScale_bounds N hN j hj
    have hmi0 : 0 ≤ dyadicScale i := by linarith
    have hnj0 : 0 ≤ dyadicScale j := by linarith
    have hB'nn : 0 ≤ (C + 2 * A + 1) * (dyadicScale i * dyadicScale j) ^ (ε / 2) *
        (dyadicScale i + dyadicScale j) :=
      mul_nonneg (mul_nonneg hC' (Real.rpow_nonneg (mul_nonneg hmi0 hnj0) _))
        (by linarith)
    have hsub := DedekindZetaZeroFree.LargeSieve.Vendor.finite_subrange_bound
      (idealDyadicBlock F c i) (clippedDyadicBlock F c M i)
      (idealDyadicBlock F c j) (clippedDyadicBlock F c N j)
      (clippedDyadicBlock_subset_idealDyadicBlock F c M i)
      (clippedDyadicBlock_subset_idealDyadicBlock F c N j)
      (fun b a => (𝓕.χ b) a)
      ((C + 2 * A + 1) * (dyadicScale i * dyadicScale j) ^ (ε / 2) *
        (dyadicScale i + dyadicScale j)) hB'nn (hub i j)
    have hBle : (C + 2 * A + 1) * (dyadicScale i * dyadicScale j) ^ (ε / 2) *
        (dyadicScale i + dyadicScale j) ≤
        (C + 2 * A + 1) * ((M * N) ^ (ε / 2)) * (M + N) := by
      have hmn : dyadicScale i * dyadicScale j ≤ M * N :=
        mul_le_mul hmiM hnjN hnj0 hM0.le
      have hpow : (dyadicScale i * dyadicScale j) ^ (ε / 2) ≤ (M * N) ^ (ε / 2) :=
        Real.rpow_le_rpow (mul_nonneg hmi0 hnj0) hmn hηle
      have hsum : dyadicScale i + dyadicScale j ≤ M + N := by linarith
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hC') hsum (by linarith)
        (mul_nonneg hC' (Real.rpow_nonneg hMN0.le _))
    exact le_trans (hsub lam)
      (mul_le_mul_of_nonneg_right hBle (Finset.sum_nonneg fun b _ => sq_nonneg _))
  have hpart := DedekindZetaZeroFree.LargeSieve.Vendor.finite_partition_quadratic_bound
    (idealAdmissibleFinset F c M) (idealAdmissibleFinset F c N)
    (Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength M + 1))
    (Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength N + 1))
    (clippedDyadicBlock F c M) (clippedDyadicBlock F c N)
    (biUnion_clippedDyadicBlock F c M hM).symm (biUnion_clippedDyadicBlock F c N hN).symm
    (pairwiseDisjoint_clippedDyadicBlock F c M hM)
    (pairwiseDisjoint_clippedDyadicBlock F c N hN)
    (fun b a => (𝓕.χ b) a) lam
    ((C + 2 * A + 1) * ((M * N) ^ (ε / 2)) * (M + N)) hBbig_nn hblock
  have hcM : ((Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength M + 1)).card : ℝ) ≤
      k * M ^ (ε / 2) := by
    rw [Finset.card_range, hkdef]
    push_cast
    exact DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength_small_power hη hM
  have hcN : ((Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength N + 1)).card : ℝ) ≤
      k * N ^ (ε / 2) := by
    rw [Finset.card_range, hkdef]
    push_cast
    exact DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength_small_power hη hN
  have hcard : ((Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength M + 1)).card : ℝ) *
      ((Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength N + 1)).card : ℝ) ≤
      k ^ 2 * (M * N) ^ (ε / 2) := by
    have h1 : ((Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength M + 1)).card : ℝ) *
        ((Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength N + 1)).card : ℝ) ≤
        (k * M ^ (ε / 2)) * (k * N ^ (ε / 2)) :=
      mul_le_mul hcM hcN (Nat.cast_nonneg _) (mul_nonneg hk.le (Real.rpow_nonneg hM0.le _))
    have h2 : (k * M ^ (ε / 2)) * (k * N ^ (ε / 2)) = k ^ 2 * (M * N) ^ (ε / 2) := by
      rw [Real.mul_rpow hM0.le hN0.le]
      ring
    exact h1.trans h2.le
  have hfinal : ((Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength M + 1)).card : ℝ) *
      ((Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength N + 1)).card : ℝ) *
      ((C + 2 * A + 1) * ((M * N) ^ (ε / 2)) * (M + N)) ≤
      (C + 2 * A + 1) * k ^ 2 * (M * N) ^ ε * (M + N) := by
    have h1 := mul_le_mul_of_nonneg_right hcard hBbig_nn
    have h2 : k ^ 2 * (M * N) ^ (ε / 2) *
        ((C + 2 * A + 1) * ((M * N) ^ (ε / 2)) * (M + N)) =
        (C + 2 * A + 1) * k ^ 2 * ((M * N) ^ (ε / 2) * (M * N) ^ (ε / 2)) *
          (M + N) := by
      ring
    have h3 : (M * N) ^ (ε / 2) * (M * N) ^ (ε / 2) = (M * N) ^ ε := by
      rw [← Real.rpow_add hMN0 (ε / 2) (ε / 2)]
      congr 1
      ring
    calc ((Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength M + 1)).card : ℝ) *
          ((Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength N + 1)).card : ℝ) *
          ((C + 2 * A + 1) * ((M * N) ^ (ε / 2)) * (M + N))
        ≤ k ^ 2 * (M * N) ^ (ε / 2) *
            ((C + 2 * A + 1) * ((M * N) ^ (ε / 2)) * (M + N)) := h1
      _ = (C + 2 * A + 1) * k ^ 2 * ((M * N) ^ (ε / 2) * (M * N) ^ (ε / 2)) *
            (M + N) := h2
      _ = (C + 2 * A + 1) * k ^ 2 * (M * N) ^ ε * (M + N) := by rw [h3]
  calc ∑ a ∈ idealAdmissibleFinset F c M,
        ‖∑ b ∈ idealAdmissibleFinset F c N, lam b * (𝓕.χ b) a‖ ^ 2
      ≤ ((Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength M + 1)).card : ℝ) *
          ((Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength N + 1)).card : ℝ) *
          ((C + 2 * A + 1) * ((M * N) ^ (ε / 2)) * (M + N)) *
          ∑ b ∈ idealAdmissibleFinset F c N, ‖lam b‖ ^ 2 := hpart
    _ ≤ (C + 2 * A + 1) * k ^ 2 * (M * N) ^ ε * (M + N) *
          ∑ b ∈ idealAdmissibleFinset F c N, ‖lam b‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hfinal henergy_nn

end DedekindZetaZeroFree.LargeSieve.Sieve
