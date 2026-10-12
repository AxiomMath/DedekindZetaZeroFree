module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Irreducible
public import DedekindZetaZeroFree.RepresentationTheory.Continuous.IntertwiningMaps

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Continuous/Schur.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

namespace ContRepresentation

section Scalar

variable {𝕜 G V : Type*} [Field 𝕜] [IsAlgClosed 𝕜] [Monoid G]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousConstSMul 𝕜 V] [FiniteDimensional 𝕜 V]

variable (π : ContRepresentation 𝕜 G V)

theorem exists_eq_smul_one_of_isIrreducible
    (hirr : Representation.IsIrreducible π.toRepresentation) (f : ContIntertwiningMap π π) :
    ∃ c : 𝕜, f = c • 1 := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := π.toRepresentation)).2 f.toIntertwiningMap
  refine ⟨c, ContIntertwiningMap.ext <| ContinuousLinearMap.ext fun v ↦ ?_⟩
  simpa [Algebra.algebraMap_eq_smul_one, ContIntertwiningMap.smul_apply,
    ContIntertwiningMap.one_apply] using congr($hc.symm v)

theorem eq_finrank_inv_mul_trace_smul_id_of_isIrreducible
    (hdim : (Module.finrank 𝕜 V : 𝕜) ≠ 0)
    (hirr : Representation.IsIrreducible π.toRepresentation) (f : ContIntertwiningMap π π) :
    f.toContinuousLinearMap
      = ((Module.finrank 𝕜 V : 𝕜)⁻¹ *
          LinearMap.trace 𝕜 V (f.toContinuousLinearMap : V →ₗ[𝕜] V)) •
        ContinuousLinearMap.id 𝕜 V := by
  obtain ⟨c, rfl⟩ := π.exists_eq_smul_one_of_isIrreducible hirr f
  ext v
  simp [mul_comm c, inv_mul_cancel_left₀ hdim]

end Scalar

end ContRepresentation
