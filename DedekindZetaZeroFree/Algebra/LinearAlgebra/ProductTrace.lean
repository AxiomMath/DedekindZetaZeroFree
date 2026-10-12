module

public import Mathlib.LinearAlgebra.Trace
public import DedekindZetaZeroFree.Algebra.LinearAlgebra.CoordinateVectorSeparation

/-
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/LinearAlgebra/Trace/Pi.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
-/

@[expose] public section

namespace DedekindZetaZeroFree.TauCeti

universe u v w

variable {k : Type u} {ι : Type v} {M : Type w}
  [CommRing k] [Fintype ι]
  [AddCommGroup M] [Module k M] [Module.Free k M] [Module.Finite k M]

@[simp]
theorem _root_.LinearMap.trace_piMap {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)] [∀ i, Module.Free k (M i)]
    [∀ i, Module.Finite k (M i)] (f : ∀ i, M i →ₗ[k] M i) :
    LinearMap.trace k ((i : ι) → M i) (LinearMap.piMap f) =
      ∑ i, LinearMap.trace k (M i) (f i) := by
  classical
  let b (i : ι) := Module.Free.chooseBasis k (M i)
  rw [LinearMap.trace_eq_matrix_trace k (Pi.basis b), LinearMap.toMatrix_piMap b b,
    Matrix.trace_blockDiagonal']
  simp_rw [LinearMap.trace_eq_matrix_trace k (b _)]

end DedekindZetaZeroFree.TauCeti
