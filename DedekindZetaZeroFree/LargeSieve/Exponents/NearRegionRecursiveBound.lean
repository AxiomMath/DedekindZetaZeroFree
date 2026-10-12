module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.QuadraticFormsAndSieveExponents
public import DedekindZetaZeroFree.LargeSieve.Exponents.RecursionParameterEstimates

@[expose] public section

noncomputable section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve

theorem recursion_near_region (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (α : ℝ) (hα : 1 ≤ α) (hE : HasSieveExponent F c Q α)
    (η : ℝ) (hη : 0 < η) :
    let r : ℕ := max 1 ⌈20 / η⌉₊
    let δ : ℝ := η / (8 * (r : ℝ) * (α + 1))
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
        M ≤ 2 * N * Real.rpow (M * N) δ →
        B1 F c Q M N ≤ C * Real.rpow (M * N) η *
          (M + N + Real.rpow N (2 * α - 1) * Real.rpow M (1 - α)) := by
  dsimp only
  obtain ⟨C0, hC0, hC0b⟩ := hE (η / 4) (by linarith)
  refine ⟨C0 * Real.rpow 2 (α - 1), mul_nonneg hC0 (Real.rpow_nonneg (by norm_num) _), ?_⟩
  intro M N hM hN hnear
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hTpos : 0 < M * N := mul_pos (by linarith) (by linarith)
  have hr : 1 ≤ max 1 ⌈20 / η⌉₊ := le_max_left _ _
  have hrη : 20 / η ≤ ((max 1 ⌈20 / η⌉₊ : ℕ) : ℝ) := by
    refine le_trans (Nat.le_ceil (20 / η)) ?_
    exact_mod_cast le_max_right 1 ⌈20 / η⌉₊
  obtain ⟨h1, h2⟩ :=
    recursion_parameter_near α M N η (max 1 ⌈20 / η⌉₊) hα hM hN hη hr hrη hnear
  set d : ℝ := η / (8 * ((max 1 ⌈20 / η⌉₊ : ℕ) : ℝ) * (α + 1)) with hd
  set X : ℝ := Real.rpow N (2 * α - 1) * Real.rpow M (1 - α) with hX
  set cc : ℝ := Real.rpow 2 (α - 1) * Real.rpow (M * N) (d * (α - 1)) with hcc
  have hd0 : 0 < d := by
    rw [hd]
    apply div_pos hη
    have : (1 : ℝ) ≤ ((max 1 ⌈20 / η⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast le_max_left 1 ⌈20 / η⌉₊
    nlinarith [hα, this]
  have hXnn : 0 ≤ X := by
    rw [hX]; exact mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hM0 _)
  have hcc1 : 1 ≤ cc := by
    rw [hcc]
    refine one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by norm_num) (by linarith)) ?_
    exact Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hM hN)
      (mul_nonneg hd0.le (by linarith))
  have hcc0 : 0 ≤ cc := le_trans zero_le_one hcc1
  have hNle : Real.rpow N α ≤ cc * X := by
    rw [hX, ← mul_assoc]
    exact h1
  have key : M + Real.rpow N α ≤ cc * (M + N + X) := by
    have hMle : M ≤ cc * M := le_mul_of_one_le_left hM0 hcc1
    calc M + Real.rpow N α ≤ cc * M + cc * X := add_le_add hMle hNle
      _ = cc * (M + X) := by ring
      _ ≤ cc * (M + N + X) := by
            apply mul_le_mul_of_nonneg_left _ hcc0
            linarith [hN0, hXnn]
  have hsplit : Real.rpow (M * N) (η / 4 + d * (α - 1)) =
      Real.rpow (M * N) (η / 4) * Real.rpow (M * N) (d * (α - 1)) :=
    Real.rpow_add hTpos _ _
  have hstep1 : C0 * Real.rpow 2 (α - 1) * Real.rpow (M * N) (η / 4 + d * (α - 1)) *
        (M + N + X) ≤
      C0 * Real.rpow 2 (α - 1) * Real.rpow (M * N) η * (M + N + X) := by
    have hfac : 0 ≤ C0 * Real.rpow 2 (α - 1) * (M + N + X) :=
      mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (by norm_num) _))
        (by linarith [hM0, hN0, hXnn])
    calc C0 * Real.rpow 2 (α - 1) * Real.rpow (M * N) (η / 4 + d * (α - 1)) *
            (M + N + X)
        = (C0 * Real.rpow 2 (α - 1) * (M + N + X)) *
            Real.rpow (M * N) (η / 4 + d * (α - 1)) := by ring
      _ ≤ (C0 * Real.rpow 2 (α - 1) * (M + N + X)) * Real.rpow (M * N) η :=
            mul_le_mul_of_nonneg_left h2 hfac
      _ = C0 * Real.rpow 2 (α - 1) * Real.rpow (M * N) η * (M + N + X) := by ring
  calc B1 F c Q M N
      ≤ C0 * Real.rpow (M * N) (η / 4) * (M + Real.rpow N α) := hC0b M N hM hN
    _ ≤ C0 * Real.rpow (M * N) (η / 4) * (cc * (M + N + X)) :=
          mul_le_mul_of_nonneg_left key (mul_nonneg hC0 (Real.rpow_nonneg hTpos.le _))
    _ = C0 * Real.rpow 2 (α - 1) * Real.rpow (M * N) (η / 4 + d * (α - 1)) *
          (M + N + X) := by
          rw [hcc, hsplit]; ring
    _ ≤ C0 * Real.rpow 2 (α - 1) * Real.rpow (M * N) η * (M + N + X) := hstep1

end DedekindZetaZeroFree.LargeSieve.Sieve

end
