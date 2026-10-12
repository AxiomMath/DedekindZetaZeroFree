module

public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/LinearAlgebra/Matrix/Diagonal.lean`. Original Apache-2.0 copyright and authors retained.
-/

@[expose] public section

open Matrix

namespace DedekindZetaZeroFree.TauCeti

variable {m n : Type*} [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

variable {A : Type*} [NonUnitalNonAssocSemiring A] {i : m} {j : n}

@[simp]
theorem diagonal_mul_single_mul_diagonal {v : m → A} {w : n → A} (c : A) :
    diagonal v * single i j c * diagonal w = single i j (v i * c * w j) := by
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [h]

end DedekindZetaZeroFree.TauCeti
