module

public import DedekindZetaZeroFree.Analysis.NormedModules.ContinuousTrace
public import DedekindZetaZeroFree.RepresentationTheory.Continuous.MatrixCoefficients
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Analysis.InnerProductSpace.Trace

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Continuous/Character.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open scoped InnerProductSpace

open DedekindZetaZeroFree.TauCeti DedekindZetaZeroFree.TauCeti.ContRepresentation

namespace ContRepresentation

section Monoid

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [TopologicalSpace G] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

noncomputable def character (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) : C(G, 𝕜) where
  toFun := π.toRepresentation.character
  continuous_toFun := by
    have h : π.toRepresentation.character = fun g ↦ traceCLM 𝕜 V (π g) := by
      funext g
      rw [traceCLM_apply]
      rfl
    rw [h]
    exact (traceCLM 𝕜 V).continuous.comp hπ

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

theorem coe_character : ⇑(character π hπ) = π.toRepresentation.character :=
  (rfl)

@[simp]
theorem character_apply (g : G) :
    character π hπ g = LinearMap.trace 𝕜 V (π g : V →ₗ[𝕜] V) :=
  (rfl)

@[simp]
theorem character_trivial :
    character (ContRepresentation.trivial 𝕜 G V) continuous_const =
      ContinuousMap.const G (Module.finrank 𝕜 V : 𝕜) := by
  ext g
  have hid : ((ContRepresentation.trivial 𝕜 G V g : V →L[𝕜] V) : V →ₗ[𝕜] V) = LinearMap.id :=
    LinearMap.ext fun v ↦ ContRepresentation.trivial_apply (R := 𝕜) (G := G) (V := V) g v

  rw [character_apply (ContRepresentation.trivial 𝕜 G V) continuous_const, hid,
    LinearMap.trace_id, ContinuousMap.const_apply]

@[simp]
theorem character_restrict {H : Type*} [Monoid H] [TopologicalSpace H] (φ : H →* G)
    (hφ : Continuous φ) :
    character (π.restrict φ) (hπ.comp hφ) = (character π hπ).comp ⟨φ, hφ⟩ := by
  ext h
  rw [character_apply, ContinuousMap.comp_apply, character_apply, ContinuousMap.coe_mk,
    ContRepresentation.restrict_apply]

end Monoid

section MonoidInner

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

theorem character_apply_eq_sum_inner {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι 𝕜 V) (g : G) :
    character π hπ g = ∑ i, ⟪e i, π g (e i)⟫_𝕜 :=
  LinearMap.trace_eq_sum_inner _ e

theorem star_character {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι 𝕜 V) :
    star (character π hπ) = ∑ i, matrixCoeff π hπ (e i) (e i) := by
  ext g
  rw [ContinuousMap.star_apply, character_apply_eq_sum_inner π hπ e g]
  simp [inner_conj_symm]

end MonoidInner

section Group

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Group G]
  [TopologicalSpace G] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

theorem character_conj (g h : G) :
    character π hπ (h * g * h⁻¹) = character π hπ g :=
  Representation.char_conj π.toRepresentation g h

end Group

end ContRepresentation
