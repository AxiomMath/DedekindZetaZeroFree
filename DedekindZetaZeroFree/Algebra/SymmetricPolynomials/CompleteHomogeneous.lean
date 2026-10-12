module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import DedekindZetaZeroFree.Algebra.SymmetricTuples.Enumeration

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RingTheory/MvPolynomial/Symmetric/Complete.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

namespace DedekindZetaZeroFree.TauCeti

theorem eval_hsymm {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R] (f : σ → R)
    (d : ℕ) : MvPolynomial.eval f (MvPolynomial.hsymm σ R d)
      = ∑ s : Sym σ d, ((s : Multiset σ).map f).prod := by
  rw [MvPolynomial.hsymm, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_multiset_prod, Multiset.map_map]
  simp [Function.comp_def]

theorem eval_hsymm_fin_two {R : Type*} [CommSemiring R] (f : Fin 2 → R) (d : ℕ) :
    MvPolynomial.eval f (MvPolynomial.hsymm (Fin 2) R d)
      = ∑ i ∈ Finset.range (d + 1), f 0 ^ i * f 1 ^ (d - i) := by
  rw [eval_hsymm, ← Fin.sum_univ_eq_sum_range _ (d + 1),
    ← Equiv.sum_comp (symFinTwoEquiv d).symm]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [coe_symFinTwoEquiv_symm_apply]
  simp

end DedekindZetaZeroFree.TauCeti
