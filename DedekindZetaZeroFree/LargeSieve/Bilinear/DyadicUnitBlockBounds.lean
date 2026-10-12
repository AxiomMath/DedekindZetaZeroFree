module

public import DedekindZetaZeroFree.Arithmetic.Ideals.DyadicNormBlocks
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.CharacterValues

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

private theorem sum_norm_sq_le_card_mul (S : Finset (Ideal (𝓞 F)))
    (f : Ideal (𝓞 F) → ℂ) :
    ‖∑ i ∈ S, f i‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖f i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ S, f i‖ ≤ ∑ i ∈ S, ‖f i‖ := norm_sum_le _ _
  have h2 : (∑ i ∈ S, ‖f i‖) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖f i‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
    simpa using this
  calc ‖∑ i ∈ S, f i‖ ^ 2 ≤ (∑ i ∈ S, ‖f i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

private theorem squarefree_top_ideal : Squarefree (⊤ : Ideal (𝓞 F)) := by
  have h : (⊤ : Ideal (𝓞 F)) = 1 := Ideal.one_eq_top.symm
  rw [h]
  exact squarefree_one

private theorem unit_row_bound (c : Ideal (𝓞 F))
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) (S : Finset (Ideal (𝓞 F)))
    (lam : Ideal (𝓞 F) → ℂ) :
    (∑ _a ∈ ({⊤} : Finset (Ideal (𝓞 F))),
      ‖∑ b ∈ S, lam b * (Q.χ b) _a‖ ^ 2) ≤
      (S.card : ℝ) * ∑ b ∈ S, ‖lam b‖ ^ 2 := by
  rw [Finset.sum_singleton]
  have h : (∑ b ∈ S, lam b * (Q.χ b) ⊤) = ∑ b ∈ S, lam b := by
    refine Finset.sum_congr rfl ?_
    intro b _
    rw [show (Q.χ b) ⊤ = 1 from (Q.χ b).map_top', mul_one]
  rw [h]
  exact sum_norm_sq_le_card_mul S lam

private theorem unit_column_bound (c : Ideal (𝓞 F))
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) (S : Finset (Ideal (𝓞 F)))
    (lam : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ S, ‖∑ _b ∈ ({⊤} : Finset (Ideal (𝓞 F))), lam _b * (Q.χ _b) a‖ ^ 2) ≤
      (S.card : ℝ) * ‖lam ⊤‖ ^ 2 := by
  have hbound : ∀ a ∈ S,
      ‖∑ _b ∈ ({⊤} : Finset (Ideal (𝓞 F))), lam _b * (Q.χ _b) a‖ ^ 2 ≤ ‖lam ⊤‖ ^ 2 := by
    intro a _
    rw [Finset.sum_singleton, norm_mul, mul_pow]
    have h1 : ‖(Q.χ ⊤) a‖ ^ 2 ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (quadraticFamily_norm_le_one Q squarefree_top_ideal (by simp) a)
    calc ‖lam ⊤‖ ^ 2 * ‖(Q.χ ⊤) a‖ ^ 2 ≤ ‖lam ⊤‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = ‖lam ⊤‖ ^ 2 := mul_one _
  calc (∑ a ∈ S, ‖∑ _b ∈ ({⊤} : Finset (Ideal (𝓞 F))), lam _b * (Q.χ _b) a‖ ^ 2)
      ≤ ∑ _a ∈ S, ‖lam ⊤‖ ^ 2 := Finset.sum_le_sum hbound
    _ = (S.card : ℝ) * ‖lam ⊤‖ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]

private theorem dyadicBlock_card_le (c : Ideal (𝓞 F)) (A : ℝ) (hA : 1 ≤ A)
    (hcount : ∀ X : ℝ, 1 ≤ X → ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) ≤ A * X)
    (j : ℕ) :
    ((idealDyadicBlock F c j).card : ℝ) ≤ A * (2 * dyadicScale j) := by
  match j with
  | 0 =>
    simp only [idealDyadicBlock, dyadicScale, Finset.card_singleton, Nat.cast_one]
    nlinarith
  | k + 1 =>
    simp only [idealDyadicBlock, dyadicScale]
    have h2 : (1 : ℝ) ≤ 2 * (2 : ℝ) ^ k := by
      have h : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      linarith
    have hle : (paperShell F c ((2 : ℝ) ^ k)).card ≤
        (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F (2 * 2 ^ k)).card := by
      refine Finset.card_le_card ?_
      intro I hI
      rw [paperShell, idealAdmissibleFinset] at hI
      simp only [Finset.mem_filter] at hI
      exact hI.1.1
    calc ((paperShell F c ((2 : ℝ) ^ k)).card : ℝ)
        ≤ ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F (2 * 2 ^ k)).card : ℝ) := by exact_mod_cast hle
      _ ≤ A * (2 * 2 ^ k) := hcount _ h2

private theorem unit_error_factor (C A δ s t : ℝ) (hC : 0 ≤ C) (hA : 1 ≤ A)
    (hδ : 0 ≤ δ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    A * (2 * s) ≤ (C + 2 * A + 1) * (s * t) ^ δ * (s + t) := by
  have hK : 0 ≤ C + 2 * A + 1 := by linarith
  have hK2 : 2 * A ≤ C + 2 * A + 1 := by linarith
  have hs0 : 0 ≤ s := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hst : (1 : ℝ) ≤ s * t := by nlinarith
  have hpow : (1 : ℝ) ≤ (s * t) ^ δ := Real.one_le_rpow hst hδ
  have hpow0 : 0 ≤ (s * t) ^ δ := by linarith
  have hsum : s ≤ s + t := by linarith
  calc A * (2 * s) = 2 * A * s := by ring
    _ ≤ (C + 2 * A + 1) * s := mul_le_mul_of_nonneg_right hK2 hs0
    _ ≤ (C + 2 * A + 1) * ((s * t) ^ δ * s) := by
        have h1 : s ≤ (s * t) ^ δ * s := by
          calc s = 1 * s := (one_mul s).symm
            _ ≤ (s * t) ^ δ * s := mul_le_mul_of_nonneg_right hpow hs0
        exact mul_le_mul_of_nonneg_left h1 hK
    _ ≤ (C + 2 * A + 1) * ((s * t) ^ δ * (s + t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hpow0) hK
    _ = (C + 2 * A + 1) * (s * t) ^ δ * (s + t) := by ring

private theorem shell_constant_le (C A δ m n E : ℝ) (hC : 0 ≤ C) (hA : 1 ≤ A)
    (hδ : 0 ≤ δ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hE : 0 ≤ E) :
    C * (m * n) ^ δ * (m + n) * E ≤ (C + 2 * A + 1) * (m * n) ^ δ * (m + n) * E := by
  have hK : C ≤ C + 2 * A + 1 := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hmn0 : 0 ≤ m * n := mul_nonneg hm0 hn0
  have hpow0 : 0 ≤ (m * n) ^ δ := Real.rpow_nonneg hmn0 δ
  have hsum0 : 0 ≤ m + n := by linarith
  have h1 : C * (m * n) ^ δ ≤ (C + 2 * A + 1) * (m * n) ^ δ :=
    mul_le_mul_of_nonneg_right hK hpow0
  have h2 : C * (m * n) ^ δ * (m + n) ≤ (C + 2 * A + 1) * (m * n) ^ δ * (m + n) :=
    mul_le_mul_of_nonneg_right h1 hsum0
  exact mul_le_mul_of_nonneg_right h2 hE

private theorem both_unit_arith (C A δ E : ℝ) (hC : 0 ≤ C) (hA : 1 ≤ A) (hE : 0 ≤ E) :
    E ≤ (C + 2 * A + 1) * (1 * 1) ^ δ * (1 + 1) * E := by
  have h1 : (1 : ℝ) ≤ (C + 2 * A + 1) * (1 * 1) ^ δ * (1 + 1) := by
    have hp : (1 * 1 : ℝ) ^ δ = 1 := by rw [one_mul, Real.one_rpow]
    rw [hp]
    nlinarith
  calc E = 1 * E := (one_mul E).symm
    _ ≤ (C + 2 * A + 1) * (1 * 1) ^ δ * (1 + 1) * E := mul_le_mul_of_nonneg_right h1 hE

theorem unit_block_extension_constant_nonneg
    (C A : ℝ) (hC : 0 ≤ C) (hA : 1 ≤ A) :
    0 ≤ C + 2 * A + 1 := by
  linarith

theorem unit_block_extension
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (𝓕 : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (δ : ℝ) (hδ : 0 ≤ δ) (C : ℝ) (hC : 0 ≤ C) (A : ℝ) (hA : 1 ≤ A)
    (hcount : ∀ X : ℝ, 1 ≤ X →
      ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) ≤ A * X)
    (hshell : ∀ M N : ℝ, 1 ≤ M → 1 ≤ N → ∀ lam : Ideal (𝓞 F) → ℂ,
      (∑ a ∈ paperShell F c M,
        ‖∑ b ∈ paperShell F c N, lam b * (𝓕.χ b) a‖ ^ 2) ≤
      C * (M * N) ^ δ * (M + N) *
        ∑ b ∈ paperShell F c N, ‖lam b‖ ^ 2) :
    ∀ i j : ℕ, ∀ lam : Ideal (𝓞 F) → ℂ,
      (∑ a ∈ idealDyadicBlock F c i,
        ‖∑ b ∈ idealDyadicBlock F c j, lam b * (𝓕.χ b) a‖ ^ 2) ≤
      (C + 2 * A + 1) * (dyadicScale i * dyadicScale j) ^ δ *
        (dyadicScale i + dyadicScale j) *
        ∑ b ∈ idealDyadicBlock F c j, ‖lam b‖ ^ 2 := by
  intro i j lam
  rcases i with _ | k
  · rcases j with _ | l
    ·
      simp only [idealDyadicBlock, dyadicScale, Finset.sum_singleton]
      rw [show (𝓕.χ ⊤) ⊤ = 1 from (𝓕.χ ⊤).map_top', mul_one]
      exact both_unit_arith C A δ _ hC hA (sq_nonneg _)
    ·
      simp only [idealDyadicBlock, dyadicScale]
      have hE : 0 ≤ ∑ b ∈ paperShell F c ((2 : ℝ) ^ l), ‖lam b‖ ^ 2 :=
        Finset.sum_nonneg (fun b _ => sq_nonneg _)
      have hcard := dyadicBlock_card_le c A hA hcount (l + 1)
      simp only [idealDyadicBlock, dyadicScale] at hcard
      have hfac := unit_error_factor C A δ ((2 : ℝ) ^ l) 1 hC hA hδ
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (by norm_num)
      refine le_trans (unit_row_bound c 𝓕 (paperShell F c ((2 : ℝ) ^ l)) lam) ?_
      refine le_trans (mul_le_mul_of_nonneg_right hcard hE) ?_
      refine le_trans (mul_le_mul_of_nonneg_right hfac hE) ?_
      exact le_of_eq (by rw [mul_one, one_mul, add_comm (1 : ℝ) ((2 : ℝ) ^ l)])
  · rcases j with _ | l
    ·
      simp only [idealDyadicBlock, dyadicScale]
      have hE : 0 ≤ ‖lam ⊤‖ ^ 2 := sq_nonneg _
      have hcard := dyadicBlock_card_le c A hA hcount (k + 1)
      simp only [idealDyadicBlock, dyadicScale] at hcard
      have hfac := unit_error_factor C A δ ((2 : ℝ) ^ k) 1 hC hA hδ
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (by norm_num)
      refine le_trans (unit_column_bound c 𝓕 (paperShell F c ((2 : ℝ) ^ k)) lam) ?_
      refine le_trans (mul_le_mul_of_nonneg_right hcard hE) ?_
      refine le_trans (mul_le_mul_of_nonneg_right hfac hE) ?_
      exact le_of_eq (by rw [Finset.sum_singleton])
    ·
      simp only [idealDyadicBlock, dyadicScale, one_mul, mul_one]
      refine le_trans (hshell ((2 : ℝ) ^ k) ((2 : ℝ) ^ l)
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) lam) ?_
      exact shell_constant_le C A δ ((2 : ℝ) ^ k) ((2 : ℝ) ^ l) _
        hC hA hδ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        (Finset.sum_nonneg (fun b _ => sq_nonneg _))

end DedekindZetaZeroFree.LargeSieve.Sieve
