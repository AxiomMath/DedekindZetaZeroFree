module

public import DedekindZetaZeroFree.RepresentationTheory.Continuous.Characters

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Continuous/LinHom.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open DedekindZetaZeroFree.TauCeti DedekindZetaZeroFree.TauCeti.ContRepresentation

namespace ContRepresentation

section Definition

variable {𝕜 G V W : Type*} [NontriviallyNormedField 𝕜] [Group G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

noncomputable def linHom (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W) :
    ContRepresentation 𝕜 G (V →L[𝕜] W) :=
  .ofMonoidHom
    { toFun g := (ContinuousLinearMap.compL 𝕜 V W W (ρ g)).comp
        ((ContinuousLinearMap.compL 𝕜 V V W).flip (π g⁻¹))
      map_one' := by
        ext T v
        simp [ContinuousLinearMap.compL_apply, ContinuousLinearMap.one_def]
      map_mul' g h := by
        ext T v
        simp [ContinuousLinearMap.compL_apply, mul_inv_rev, map_mul π, map_mul ρ,
          mul_apply_eq_comp] }

variable (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)

@[simp]
theorem linHom_apply (g : G) (T : V →L[𝕜] W) :
    (linHom π ρ) g T = (ρ g).comp (T.comp (π g⁻¹)) :=
  (rfl)

end Definition

section Invariants

variable {𝕜 G V W : Type*} [NontriviallyNormedField 𝕜] [Group G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)

@[simp]
theorem linHom_apply_eq_self_iff_isIntertwining (T : V →L[𝕜] W) :
    (∀ g : G, (ρ g).comp (T.comp (π g⁻¹)) = T) ↔ ∀ g : G, T.comp (π g) = (ρ g).comp T := by
  have key := Representation.mem_linHom_invariants_iff_isIntertwining (ρ := π.toRepresentation)
    (σ := ρ.toRepresentation) (T : V →ₗ[𝕜] W)
  rw [Representation.isIntertwiningMap_iff] at key
  simp only [LinearMap.ext_iff, LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at key
  simp only [ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply]
  exact key

end Invariants

end ContRepresentation
