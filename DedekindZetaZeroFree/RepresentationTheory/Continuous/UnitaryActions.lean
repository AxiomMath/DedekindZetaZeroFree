module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import DedekindZetaZeroFree.RepresentationTheory.Continuous.Subrepresentations

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Continuous/Unitary/Basic.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

/-
https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md
Daniel Bump, Lie Groups, second edition, Chapters 2–4.
-/

open scoped InnerProductSpace

namespace DedekindZetaZeroFree.TauCeti

namespace ContRepresentation

variable {R G V : Type*} [Ring R] [Group G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V]

private theorem self_inv_apply (π : ContRepresentation R G V) (g : G) (v : V) :
    π g (π g⁻¹ v) = v :=
  Representation.self_inv_apply π.toRepresentation g v

section Monoid

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

def IsUnitary (π : ContRepresentation 𝕜 G V) : Prop :=
  ∀ g v w, ⟪π g v, π g w⟫_𝕜 = ⟪v, w⟫_𝕜

theorem isUnitary_iff_norm_map (π : ContRepresentation 𝕜 G V) :
    IsUnitary π ↔ ∀ g v, ‖π g v‖ = ‖v‖ := by
  constructor
  · intro hπ g
    exact (LinearMap.norm_map_iff_inner_map_map (π g)).mpr (hπ g)
  · intro hπ g
    exact (LinearMap.norm_map_iff_inner_map_map (π g)).mp (hπ g)

namespace IsUnitary

variable {π : ContRepresentation 𝕜 G V}

@[simp]
theorem inner_map_map (hπ : IsUnitary π) (g : G) (v w : V) :
    ⟪π g v, π g w⟫_𝕜 = ⟪v, w⟫_𝕜 :=
  hπ g v w

@[simp]
theorem norm_map (hπ : IsUnitary π) (g : G) (v : V) :
    ‖π g v‖ = ‖v‖ :=
  (isUnitary_iff_norm_map π).mp hπ g v

section

variable [CompleteSpace V]

theorem adjoint_comp_self (hπ : IsUnitary π) (g : G) :
    (ContinuousLinearMap.adjoint (π g)).comp (π g) = 1 :=
  (π g).inner_map_map_iff_adjoint_comp_self.mp (hπ g)

end

end IsUnitary

end Monoid

section Group

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable {π : ContRepresentation 𝕜 G V}

namespace IsUnitary

omit [CompleteSpace V] in

theorem inner_map_left (hπ : IsUnitary π) (g : G) (v w : V) :
    ⟪π g v, w⟫_𝕜 = ⟪v, π g⁻¹ w⟫_𝕜 := by
  simpa only [ContRepresentation.self_inv_apply] using hπ.inner_map_map g v (π g⁻¹ w)

omit [CompleteSpace V] in

theorem inner_map_right (hπ : IsUnitary π) (g : G) (v w : V) :
    ⟪v, π g w⟫_𝕜 = ⟪π g⁻¹ v, w⟫_𝕜 := by
  simpa only [ContRepresentation.self_inv_apply] using hπ.inner_map_map g (π g⁻¹ v) w

@[simp]
theorem adjoint_eq_inv (hπ : IsUnitary π) (g : G) :
    ContinuousLinearMap.adjoint (π g) = π g⁻¹ := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  simpa using hπ.inner_map_left g⁻¹ v w

end IsUnitary

end Group

end ContRepresentation

end DedekindZetaZeroFree.TauCeti
