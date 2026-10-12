module

public import DedekindZetaZeroFree.Algebra.SymmetricPower.BasisAndTrace

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/LinearAlgebra/SymmetricPower/Coordinates.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

open Finset Module

universe v w

variable {R : Type} {M : Type v} {κ : Type w} {n : ℕ}

namespace SymmetricPower

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

private theorem prod_eq_of_ofFn_eq (c : κ → R) {p q : Fin n → κ}
    (h : DedekindZetaZeroFree.TauCeti.Sym.ofFn p = DedekindZetaZeroFree.TauCeti.Sym.ofFn q) : ∏ i, c (p i) = ∏ i, c (q i) := by
  obtain ⟨σ, rfl⟩ := DedekindZetaZeroFree.TauCeti.Sym.ofFn_eq_ofFn_iff.1 h
  exact (Equiv.prod_comp σ fun i => c (p i)).symm

private theorem eq_const_of_ofFn_eq_ofFn_const {p : Fin n → κ} {k : κ}
    (h : DedekindZetaZeroFree.TauCeti.Sym.ofFn p = DedekindZetaZeroFree.TauCeti.Sym.ofFn fun _ => k) : p = fun _ => k := by
  obtain ⟨σ, hσ⟩ := DedekindZetaZeroFree.TauCeti.Sym.ofFn_eq_ofFn_iff.1 h
  exact funext fun i => by simpa using congrFun hσ (σ.symm i)

variable (b : Basis κ R M)

private theorem repr_basis_symmetricPower_tprod_smul_basis [DecidableEq κ] (c : Fin n → R)
    (p : Fin n → κ) (s : Sym κ n) :
    (b.symmetricPower n).repr (⨂ₛ[R] i, c i • b (p i)) s =
      if DedekindZetaZeroFree.TauCeti.Sym.ofFn p = s then ∏ i, c i else 0 := by
  have hbasis : (tprod R fun i => b (p i)) = b.symmetricPower n (DedekindZetaZeroFree.TauCeti.Sym.ofFn p) := by
    rw [Basis.symmetricPower_apply, tprodOfSym_ofFn]
  rw [(tprod R).map_smul_univ c fun i => b (p i), hbasis, map_smul, Basis.repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]

theorem repr_basis_symmetricPower_tprod [Fintype κ] [DecidableEq κ] (v : Fin n → M) (s : Sym κ n) :
    (b.symmetricPower n).repr (⨂ₛ[R] i, v i) s =
      ∑ p ∈ {p : Fin n → κ | DedekindZetaZeroFree.TauCeti.Sym.ofFn p = s}, ∏ i, b.repr (v i) (p i) := by
  have hv : (⨂ₛ[R] i, v i) = ⨂ₛ[R] i, ∑ k, b.repr (v i) k • b k :=
    congrArg _ (funext fun i => (b.sum_repr (v i)).symm)
  rw [hv, (tprod R).map_sum fun (i : Fin n) (k : κ) => b.repr (v i) k • b k, map_sum,
    Finsupp.finsetSum_apply, Finset.sum_filter]
  exact Finset.sum_congr rfl fun p _ =>
    repr_basis_symmetricPower_tprod_smul_basis b (fun i => b.repr (v i) (p i)) p s

@[simp]
theorem repr_basis_symmetricPower_tprod_ofFn_const (v : Fin n → M) (k : κ) :
    (b.symmetricPower n).repr (⨂ₛ[R] i, v i) (DedekindZetaZeroFree.TauCeti.Sym.ofFn fun _ => k) =
      ∏ i, b.repr (v i) k := by
  classical
  have hvi : ∀ i, ∑ j ∈ insert k (b.repr (v i)).support, b.repr (v i) j • b j = v i := fun i => by
    conv_rhs => rw [← b.linearCombination_repr (v i), Finsupp.linearCombination_apply, Finsupp.sum]
    exact (Finset.sum_subset (Finset.subset_insert k _)
      fun j _ hj => by rw [Finsupp.notMem_support_iff.1 hj, zero_smul]).symm
  have hv : (⨂ₛ[R] i, v i) =
      ⨂ₛ[R] i, ∑ j ∈ insert k (b.repr (v i)).support, b.repr (v i) j • b j :=
    congrArg _ (funext fun i => (hvi i).symm)
  rw [hv, (tprod R).map_sum_finset (fun (i : Fin n) (j : κ) => b.repr (v i) j • b j)
      fun i => insert k (b.repr (v i)).support, map_sum, Finsupp.finsetSum_apply,
    Finset.sum_congr rfl fun p _ =>
      repr_basis_symmetricPower_tprod_smul_basis b (fun i => b.repr (v i) (p i)) p _,
    Finset.sum_eq_single_of_mem (fun _ => k) (by simp)]
  · simp
  · intro p _ hne
    simpa using fun h => absurd (eq_const_of_ofFn_eq_ofFn_const h) hne

end CommSemiring

section Domain

variable [CommSemiring R] [IsDomain R] [CharZero R] [AddCommMonoid M] [Module R M]
variable (b : Basis κ R M)

theorem repr_basis_symmetricPower_tprod_const_ne_zero {u : M}
    (hu : ∀ k, b.repr u k ≠ 0) (s : Sym κ n) :
    (b.symmetricPower n).repr (⨂ₛ[R] (_ : Fin n), u) s ≠ 0 := by
  classical

  have : Finite κ := Finite.of_injective
    (fun k : κ => (⟨k, Finsupp.mem_support_iff.2 (hu k)⟩ : {j // j ∈ (b.repr u).support}))
    fun _ _ h => congrArg Subtype.val h
  have := Fintype.ofFinite κ
  obtain ⟨p₀, hp₀⟩ := DedekindZetaZeroFree.TauCeti.Sym.ofFn_surjective s
  have hne : ({p : Fin n → κ | DedekindZetaZeroFree.TauCeti.Sym.ofFn p = s} : Finset (Fin n → κ)).Nonempty :=
    ⟨p₀, by simp [hp₀]⟩
  rw [repr_basis_symmetricPower_tprod,
    Finset.sum_congr rfl fun p hp => prod_eq_of_ofFn_eq (fun k => b.repr u k) (p := p) (q := p₀)
      (by rw [(Finset.mem_filter.1 hp).2, hp₀]),
    Finset.sum_const, nsmul_eq_mul]
  exact mul_ne_zero (Nat.cast_ne_zero.2 (Finset.card_pos.2 hne).ne')
    (Finset.prod_ne_zero_iff.2 fun i _ => hu _)

end Domain

end SymmetricPower
