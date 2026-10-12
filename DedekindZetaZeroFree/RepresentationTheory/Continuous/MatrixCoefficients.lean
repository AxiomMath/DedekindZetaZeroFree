module

public import DedekindZetaZeroFree.RepresentationTheory.Continuous.UnitaryActions
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Continuous/MatrixCoefficient.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open scoped InnerProductSpace

namespace DedekindZetaZeroFree.TauCeti

namespace ContRepresentation

section Coefficients

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

noncomputable def matrixCoeff (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w : V) : C(G, 𝕜) where
  toFun g := ⟪π g v, w⟫_𝕜
  continuous_toFun := by fun_prop

@[simp]
theorem matrixCoeff_apply (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) (v w : V) (g : G) :
    matrixCoeff π hπ v w g = ⟪π g v, w⟫_𝕜 :=
  (rfl)

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

@[simp]
theorem matrixCoeff_zero_left (w : V) : matrixCoeff π hπ 0 w = 0 := by
  ext g
  simp

@[simp]
theorem matrixCoeff_zero_right (v : V) : matrixCoeff π hπ v 0 = 0 := by
  ext g
  simp

@[simp]
theorem matrixCoeff_add_left (v₁ v₂ w : V) :
    matrixCoeff π hπ (v₁ + v₂) w = matrixCoeff π hπ v₁ w + matrixCoeff π hπ v₂ w := by
  ext g
  simp [inner_add_left]

@[simp]
theorem matrixCoeff_add_right (v w₁ w₂ : V) :
    matrixCoeff π hπ v (w₁ + w₂) = matrixCoeff π hπ v w₁ + matrixCoeff π hπ v w₂ := by
  ext g
  simp [inner_add_right]

@[simp]
theorem matrixCoeff_smul_left (c : 𝕜) (v w : V) :
    matrixCoeff π hπ (c • v) w = (starRingEnd 𝕜) c • matrixCoeff π hπ v w := by
  ext g
  simp [inner_smul_left]

@[simp]
theorem matrixCoeff_smul_right (v : V) (c : 𝕜) (w : V) :
    matrixCoeff π hπ v (c • w) = c • matrixCoeff π hπ v w := by
  ext g
  simp [inner_smul_right]

noncomputable def matrixCoeffₛₗ : V →ₗ⋆[𝕜] V →ₗ[𝕜] C(G, 𝕜) where
  toFun v :=
    { toFun := matrixCoeff π hπ v
      map_add' := matrixCoeff_add_right π hπ v
      map_smul' := matrixCoeff_smul_right π hπ v }
  map_add' v₁ v₂ := LinearMap.ext fun w ↦ matrixCoeff_add_left π hπ v₁ v₂ w
  map_smul' c v := LinearMap.ext fun w ↦ matrixCoeff_smul_left π hπ c v w

@[simp]
theorem matrixCoeffₛₗ_apply_apply (v w : V) :
    matrixCoeffₛₗ π hπ v w = matrixCoeff π hπ v w :=
  (rfl)

theorem matrixCoeff_apply_mul_right (v w : V) (g g₀ : G) :
    matrixCoeff π hπ v w (g * g₀) = matrixCoeff π hπ (π g₀ v) w g := by
  simp [map_mul]

@[simp]
theorem matrixCoeff_trivial (v w : V) :
    matrixCoeff (ContRepresentation.trivial 𝕜 G V) continuous_const v w =
      ContinuousMap.const G ⟪v, w⟫_𝕜 := by
  ext g
  simp
  rfl

@[simp]
theorem matrixCoeff_restrict {H : Type*} [Monoid H] [TopologicalSpace H] (φ : H →* G)
    (hφ : Continuous φ) (v w : V) :
    matrixCoeff (π.restrict φ) (hπ.comp hφ) v w = (matrixCoeff π hπ v w).comp ⟨φ, hφ⟩ := by
  ext h
  simp

end Coefficients

section TranslationRight

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

@[simp]
theorem matrixCoeff_comp_mulRight (v w : V) (g₀ : G) :
    (matrixCoeff π hπ v w).comp (ContinuousMap.mulRight g₀) = matrixCoeff π hπ (π g₀ v) w :=
  ContinuousMap.ext fun g ↦ matrixCoeff_apply_mul_right π hπ v w g g₀

end TranslationRight

section Group

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

variable {π : ContRepresentation 𝕜 G V}

theorem matrixCoeff_apply_mul_left (hπ : Continuous π) (hunitary : IsUnitary π) (v w : V)
    (g₀ g : G) :
    matrixCoeff π hπ v w (g₀ * g) = matrixCoeff π hπ v (π g₀⁻¹ w) g := by
  have hmul : π (g₀ * g) v = π g₀ (π g v) := by simp [map_mul]
  rw [matrixCoeff_apply, matrixCoeff_apply, hmul, hunitary.inner_map_left]

theorem matrixCoeff_apply_inv (hπ : Continuous π) (hunitary : IsUnitary π) (v w : V) (g : G) :
    matrixCoeff π hπ v w g⁻¹ = (starRingEnd 𝕜) (matrixCoeff π hπ w v g) := by
  rw [matrixCoeff_apply, matrixCoeff_apply, hunitary.inner_map_left, inv_inv, inner_conj_symm]

@[simp]
theorem matrixCoeff_comp_mulLeft [SeparatelyContinuousMul G] (hπ : Continuous π)
    (hunitary : IsUnitary π) (v w : V) (g₀ : G) :
    (matrixCoeff π hπ v w).comp (ContinuousMap.mulLeft g₀) = matrixCoeff π hπ v (π g₀⁻¹ w) :=
  ContinuousMap.ext fun g ↦ matrixCoeff_apply_mul_left hπ hunitary v w g₀ g

@[simp]
theorem star_matrixCoeff [ContinuousInv G] (hπ : Continuous π) (hunitary : IsUnitary π) (v w : V) :
    star (matrixCoeff π hπ v w) =
      (matrixCoeff π hπ w v).comp ⟨Inv.inv, continuous_inv⟩ :=
  ContinuousMap.ext fun g ↦ (matrixCoeff_apply_inv hπ hunitary w v g).symm

end Group

end ContRepresentation

end DedekindZetaZeroFree.TauCeti
