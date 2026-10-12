module

public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/Topology/Algebra/Module/FiniteDimension.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

namespace MultilinearMap

variable {𝕜 ι : Type*} {M : ι → Type*} {N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [Finite ι] [∀ i, AddCommGroup (M i)] [∀ i, Module 𝕜 (M i)] [∀ i, TopologicalSpace (M i)]
  [∀ i, IsTopologicalAddGroup (M i)] [∀ i, ContinuousSMul 𝕜 (M i)] [∀ i, T2Space (M i)]
  [∀ i, FiniteDimensional 𝕜 (M i)] [AddCommMonoid N] [Module 𝕜 N] [TopologicalSpace N]
  [ContinuousAdd N] [ContinuousSMul 𝕜 N]

theorem continuous_of_finiteDimensional (f : MultilinearMap 𝕜 M N) : Continuous f := by
  classical
  cases nonempty_fintype ι
  set b : ∀ i, Module.Basis (Fin (Module.finrank 𝕜 (M i))) 𝕜 (M i) :=
    fun i ↦ Module.finBasis 𝕜 (M i) with hb
  have key : ⇑f = fun m : ∀ i, M i ↦ ∑ r : ∀ i, Fin (Module.finrank 𝕜 (M i)),
      (∏ i, (b i).repr (m i) (r i)) • f fun i ↦ b i (r i) := by
    funext m
    have hm : f m = f fun i ↦ ∑ j, (b i).repr (m i) j • b i j := by
      congr 1 with i
      exact ((b i).sum_repr (m i)).symm
    rw [hm, f.map_sum]
    exact Finset.sum_congr rfl fun r _ ↦ f.map_smul_univ _ _
  rw [key]
  refine continuous_finsetSum _ fun r _ ↦ Continuous.smul ?_ continuous_const
  refine continuous_finsetProd _ fun i _ ↦ ?_
  exact (((b i).coord (r i)).continuous_of_finiteDimensional.comp
    (continuous_apply i)).congr fun m ↦ Module.Basis.coord_apply _ _ _

end MultilinearMap
