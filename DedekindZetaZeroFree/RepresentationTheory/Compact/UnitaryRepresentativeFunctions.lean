module

public import DedekindZetaZeroFree.Analysis.InnerProductSpaces.PositiveDefiniteForms
public import DedekindZetaZeroFree.RepresentationTheory.Compact.Unitarizability
public import DedekindZetaZeroFree.RepresentationTheory.Continuous.RepresentativeFunctions

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Compact/UnitaryModel.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open MeasureTheory RCLike DedekindZetaZeroFree.TauCeti DedekindZetaZeroFree.TauCeti.ContRepresentation
open scoped InnerProductSpace

namespace ContRepresentation

section Unitarization

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

local instance instCompleteSpaceUnitaryModel : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

theorem exists_isUnitary_congr (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    ∃ e : V ≃L[𝕜] V, IsUnitary (congr e π) := by
  obtain ⟨A, hA⟩ := exists_continuousLinearEquiv_inner_map_map (π.gramOperator hπ)
    (π.isSymmetric_gramOperator hπ) fun _ hv ↦ π.re_inner_gramOperator_self_pos hπ hv

  have hA' : ∀ x y : V, ⟪A x, π.gramOperator hπ (A y)⟫_𝕜 = ⟪x, y⟫_𝕜 := fun x y ↦ by
    rw [← inner_conj_symm, hA, inner_conj_symm]
  have hunitary : ∀ (g : G) (x y : V), ⟪congr A.symm π g x, congr A.symm π g y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
    intro g x y
    rw [congr_apply, congr_apply, ContinuousLinearEquiv.symm_symm,
      ← hA' (A.symm (π g (A x))) (A.symm (π g (A y))), ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply, π.inner_gramOperator_map_map hπ, hA']
  exact ⟨A.symm, (isUnitary_iff_norm_map _).mpr fun g ↦
    (LinearMap.norm_map_iff_inner_map_map _).mpr (hunitary g)⟩

end Unitarization

end ContRepresentation
