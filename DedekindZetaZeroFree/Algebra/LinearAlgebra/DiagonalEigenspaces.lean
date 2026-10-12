module

public import DedekindZetaZeroFree.Algebra.LinearAlgebra.BasisCoordinates

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/LinearAlgebra/Eigenspace/DiagonalBasis.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

namespace DedekindZetaZeroFree.TauCeti

variable {ι K V : Type*}

section CommSemiring

variable [CommSemiring K] [AddCommMonoid V] [Module K V] {f : V →ₗ[K] V} {a : ι → K}

theorem _root_.Module.Basis.repr_apply_of_apply_basis (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (w : V) (i : ι) :
    b.repr (f w) i = a i * b.repr w i := by
  have key : (Finsupp.lapply i).comp ((b.repr : V →ₗ[K] ι →₀ K).comp f)
      = (a i • Finsupp.lapply i).comp (b.repr : V →ₗ[K] ι →₀ K) := by
    refine b.ext fun j => ?_
    rcases eq_or_ne j i with rfl | hj
    · simp [hf j]
    · simp [hf j, hj]
  simpa using LinearMap.congr_fun key w

end CommSemiring

section CoordinateSubtraction

variable [CommRing K] [AddCommGroup V] [Module K V] {f : V →ₗ[K] V} {a : ι → K}

private theorem repr_sub_smul_apply (b : Module.Basis ι K V) (hf : ∀ i, f (b i) = a i • b i)
    (w : V) (j k : ι) :
    b.repr (f w - a j • w) k = (a k - a j) * b.repr w k := by
  rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
    b.repr_apply_of_apply_basis hf, smul_eq_mul, sub_mul]

private theorem support_repr_sub_smul_subset [DecidableEq ι] (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (w : V) (j : ι) :
    (b.repr (f w - a j • w)).support ⊆ (b.repr w).support.erase j := by
  intro k hk
  have hk0 : b.repr (f w - a j • w) k ≠ 0 := Finsupp.mem_support_iff.1 hk
  rw [repr_sub_smul_apply b hf w j k] at hk0
  refine Finset.mem_erase.2 ⟨?_, Finsupp.mem_support_iff.2 (right_ne_zero_of_mul hk0)⟩
  rintro rfl
  exact hk0 (by rw [sub_self, zero_mul])

end CoordinateSubtraction

section Field

variable [Field K] [AddCommGroup V] [Module K V] {f : V →ₗ[K] V} {a : ι → K}
  {W : Submodule K V}

private theorem self_mem_aux (b : Module.Basis ι K V) (hf : ∀ i, f (b i) = a i • b i)
    (ha : Function.Injective a) (hW : ∀ v ∈ W, f v ∈ W) :
    ∀ (n : ℕ) (w : V), w ∈ W → (b.repr w).support.card ≤ n →
      ∀ i : ι, b.repr w i ≠ 0 → b i ∈ W := by
  classical
  intro n
  induction n with
  | zero =>
    intro w _ hcard i hi
    have hsupp : (b.repr w).support = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    exact absurd (Finsupp.notMem_support_iff.1 (by rw [hsupp]; exact Finset.notMem_empty i)) hi
  | succ n ih =>
    intro w hw hcard i hi
    by_cases hsub : (b.repr w).support ⊆ {i}
    ·

      set c := b.repr w i
      have hmem : c⁻¹ • w ∈ W := W.smul_mem _ hw
      rwa [b.eq_smul_of_repr_support_subset_singleton hsub, smul_smul, inv_mul_cancel₀ hi,
        one_smul] at hmem
    ·
      obtain ⟨j, hjs, hji⟩ := Finset.not_subset.1 hsub
      have hjne : j ≠ i := fun h => hji (Finset.mem_singleton.2 h)
      have hmem : f w - a j • w ∈ W := W.sub_mem (hW w hw) (W.smul_mem _ hw)
      have hcard' : (b.repr (f w - a j • w)).support.card ≤ n := by
        have hle := Finset.card_le_card (support_repr_sub_smul_subset b hf w j)
        rw [Finset.card_erase_of_mem hjs] at hle
        have hpos : 0 < (b.repr w).support.card := Finset.card_pos.2 ⟨j, hjs⟩
        omega
      refine ih _ hmem hcard' i ?_
      rw [repr_sub_smul_apply b hf w j i]
      exact mul_ne_zero (sub_ne_zero.2 fun h => hjne (ha h).symm) hi

theorem _root_.Module.Basis.self_mem_of_repr_ne_zero (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (ha : Function.Injective a) (hW : ∀ v ∈ W, f v ∈ W) {w : V}
    (hw : w ∈ W) {i : ι} (hi : b.repr w i ≠ 0) : b i ∈ W :=
  self_mem_aux b hf ha hW _ w hw le_rfl i hi

theorem _root_.Module.Basis.eq_span_self_mem (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (ha : Function.Injective a) (hW : ∀ v ∈ W, f v ∈ W) :
    W = Submodule.span K {v | ∃ i : ι, b i = v ∧ v ∈ W} := by
  refine le_antisymm (fun w hw => ?_) (Submodule.span_le.2 ?_)
  · rw [← b.linearCombination_repr w, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨k, rfl, b.self_mem_of_repr_ne_zero hf ha hW hw (Finsupp.mem_support_iff.1 hk)⟩)
  · rintro v ⟨-, -, hv⟩
    exact hv

end Field

end DedekindZetaZeroFree.TauCeti
