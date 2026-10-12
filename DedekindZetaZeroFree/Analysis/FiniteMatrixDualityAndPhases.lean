module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: FiniteOperator.lean.
-/

noncomputable section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Vendor.FiniteOperator

variable {r s k l : Type*} [Fintype r] [Fintype s]
  [DecidableEq r] [DecidableEq s]

theorem operator_conjTranspose_norm (A : Matrix r s ℂ) :
    ‖A.conjTranspose.toEuclideanLin.toContinuousLinearMap‖ =
      ‖A.toEuclideanLin.toContinuousLinearMap‖ := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

private theorem operator_conj_norm_le (A : Matrix r s ℂ) :
    ‖(Matrix.toEuclideanLin (fun i j => star (A i j) : Matrix r s ℂ)).toContinuousLinearMap‖ ≤
      ‖A.toEuclideanLin.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let y : EuclideanSpace ℂ s := WithLp.toLp 2 (fun j => star (x j))
  have hy : ‖y‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.norm_sq_eq, y]
  have heq (i : r) :
      (Matrix.toEuclideanLin (fun i j => star (A i j) : Matrix r s ℂ)).toContinuousLinearMap x i =
        star (A.toEuclideanLin.toContinuousLinearMap y i) := by
    change (∑ j, star (A i j) * x j) = star (∑ j, A i j * y j)
    simp [y]
  have hz :
      ‖(Matrix.toEuclideanLin (fun i j => star (A i j) : Matrix r s ℂ)).toContinuousLinearMap x‖ =
        ‖A.toEuclideanLin.toContinuousLinearMap y‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.norm_sq_eq, heq, norm_star]
  rw [hz, ← hy]
  exact A.toEuclideanLin.toContinuousLinearMap.le_opNorm y

theorem operator_transpose_norm (A : Matrix r s ℂ) :
    ‖A.transpose.toEuclideanLin.toContinuousLinearMap‖ =
      ‖A.toEuclideanLin.toContinuousLinearMap‖ := by
  have h (B : Matrix r s ℂ) :
      ‖B.transpose.toEuclideanLin.toContinuousLinearMap‖ ≤
        ‖B.toEuclideanLin.toContinuousLinearMap‖ := by
    calc
      _ ≤ ‖B.conjTranspose.toEuclideanLin.toContinuousLinearMap‖ := by
        have h := operator_conj_norm_le B.conjTranspose
        have heq : (fun i j => star (B.conjTranspose i j) : Matrix s r ℂ) = B.transpose := by
          ext i j
          simp
        rw [heq] at h
        exact h
      _ = _ := operator_conjTranspose_norm B
  apply le_antisymm (h A)
  have h' := operator_conj_norm_le A.transpose.conjTranspose
  calc
    _ ≤ ‖A.transpose.conjTranspose.toEuclideanLin.toContinuousLinearMap‖ := by
      simpa [Matrix.transpose, Matrix.conjTranspose] using h'
    _ = _ := operator_conjTranspose_norm A.transpose

namespace Auxiliary

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

abbrev operator (A : Matrix m n ℂ) := A.toEuclideanLin.toContinuousLinearMap

omit [DecidableEq m] in
@[simp] theorem operator_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) (i : m) :
    operator A x i = ∑ j, A i j * x j := rfl

omit [DecidableEq m] in
theorem operator_zero : operator (0 : Matrix m n ℂ) = 0 := by
  ext x i
  simp

omit [DecidableEq m] in
theorem operator_add (A B : Matrix m n ℂ) : operator (A + B) = operator A + operator B := by
  ext x i
  simp [add_mul, Finset.sum_add_distrib]

omit [DecidableEq m] in
theorem operator_smul (c : ℂ) (A : Matrix m n ℂ) : operator (c • A) = c • operator A := by
  ext x i
  simp [Finset.mul_sum, mul_assoc]

omit [DecidableEq m] in
theorem operator_sum {κ : Type*} (S : Finset κ) (A : κ → Matrix m n ℂ) :
    operator (∑ k ∈ S, A k) = ∑ k ∈ S, operator (A k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [operator_zero]
  | @insert a S ha ih => simp only [Finset.sum_insert ha, operator_add, ih]

omit [DecidableEq m] in
theorem diagonal_twist_norm_le (A : Matrix m n ℂ) (l : m → ℂ) (r : n → ℂ)
    (hl : ∀ i, ‖l i‖ ≤ 1) (hr : ∀ j, ‖r j‖ ≤ 1) :
    ‖operator (fun i j => l i * A i j * r j)‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let y : EuclideanSpace ℂ n := WithLp.toLp 2 (fun j => r j * x j)
  have hy : ‖y‖ ≤ ‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro j _
    change ‖r j * x j‖ ^ 2 ≤ ‖x j‖ ^ 2
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hr j)
  have heq (i : m) : operator (fun i j => l i * A i j * r j) x i = l i * operator A y i := by
    simp only [operator_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change l i * A i j * r j * x j = l i * (A i j * (r j * x j))
    ring
  have hz : ‖operator (fun i j => l i * A i j * r j) x‖ ≤ ‖operator A y‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    rw [heq, norm_mul]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_of_le_one_left (norm_nonneg _) (hl i)
  exact hz.trans ((operator A).le_opNorm y |>.trans
    (mul_le_mul_of_nonneg_left hy (norm_nonneg _)))

omit [DecidableEq m] in
theorem separated_decomposition_norm_le {κ : Type*} [Fintype κ]
    (A B : Matrix m n ℂ) (c : κ → ℂ) (l : κ → m → ℂ) (r : κ → n → ℂ)
    (hl : ∀ k i, ‖l k i‖ ≤ 1) (hr : ∀ k j, ‖r k j‖ ≤ 1)
    (heq : ∀ i j, A i j = ∑ k, c k * (l k i * B i j * r k j)) :
    ‖operator A‖ ≤ (∑ k, ‖c k‖) * ‖operator B‖ := by
  let T : κ → Matrix m n ℂ := fun k i j => l k i * B i j * r k j
  have hA : A = ∑ k, c k • T k := by
    ext i j
    rw [Matrix.sum_apply]
    exact heq i j
  have hOp : operator A = ∑ k, c k • operator (T k) := by
    calc
      _ = operator (∑ k, c k • T k) := congrArg operator hA
      _ = ∑ k, operator (c k • T k) := operator_sum _ _
      _ = _ := Finset.sum_congr rfl (fun k _ => operator_smul (c k) (T k))
  rw [hOp]
  calc
    _ ≤ ∑ k, ‖c k • operator (T k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖c k‖ * ‖operator B‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (diagonal_twist_norm_le B (l k) (r k) (hl k) (hr k))
        (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

end Auxiliary

theorem separated_phase_norm_le [Fintype k]
    (A : Matrix r s ℂ) (A' : Matrix s r ℂ)
    (κ : r → k) (ν : s → l) (φ : k → l → ℂ)
    (hφ : ∀ a b, ‖φ a b‖ ≤ 1)
    (hA : ∀ i j, A i j = φ (κ i) (ν j) * A' j i) :
    ‖A.toEuclideanLin.toContinuousLinearMap‖ ^ 2 ≤
      (Fintype.card k : ℝ) ^ 2 * ‖A'.toEuclideanLin.toContinuousLinearMap‖ ^ 2 := by
  classical
  have h := Auxiliary.separated_decomposition_norm_le A A'.transpose (fun _ : k => 1)
    (fun a i => if κ i = a then 1 else 0) (fun a j => φ a (ν j))
    (by intro a i; split_ifs <;> simp) (by intro a j; exact hφ a (ν j))
    (by
      intro i j
      simp only [one_mul, Matrix.transpose_apply]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simpa [mul_comm] using hA i j)
  have hn : ‖A.toEuclideanLin.toContinuousLinearMap‖ ≤
      (Fintype.card k : ℝ) * ‖A'.toEuclideanLin.toContinuousLinearMap‖ := by
    simpa [Auxiliary.operator, DedekindZetaZeroFree.LargeSieve.Vendor.FiniteOperator.operator_transpose_norm] using h
  simpa [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2

end DedekindZetaZeroFree.LargeSieve.Vendor.FiniteOperator

end
