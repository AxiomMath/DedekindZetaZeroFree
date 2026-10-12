module

public import DedekindZetaZeroFree.RepresentationTheory.Compact.IntegratedOperators

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Compact/Invariants.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open MeasureTheory DedekindZetaZeroFree.TauCeti DedekindZetaZeroFree.TauCeti.ContRepresentation

namespace ContRepresentation

section Projection

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [CompleteSpace V]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

noncomputable def orbitMap (v : V) : C(G, V) :=
  ⟨fun g ↦ π g v, (ContinuousLinearMap.apply 𝕜 V v).continuous.comp hπ⟩

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [CompleteSpace V] in

@[simp]
private theorem orbitMap_apply (v : V) (g : G) : orbitMap π hπ v g = π g v :=
  (rfl)

noncomputable def haarAverageMap : V →L[𝕜] V :=
  integratedOperator π hπ 1

theorem haarAverageMap_apply (v : V) :
    haarAverageMap π hπ v = ∫ g, π g v ∂haarProb G := by
  rw [haarAverageMap, integratedOperator_apply]
  simp

private theorem haarAverageMap_apply_eq_haarAverage (v : V) :
    haarAverageMap π hπ v = haarAverage G (𝕜 := 𝕜) (orbitMap π hπ v) := by
  rw [haarAverageMap_apply, haarAverage_apply]
  simp

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ V]
  [SMulCommClass ℝ 𝕜 V] [CompleteSpace V] in

private theorem orbitMap_comp_mulLeft (h : G) (v : V) :
    (orbitMap π hπ v).comp (ContinuousMap.mulLeft h)
      = (π h : C(V, V)).comp (orbitMap π hπ v) := by
  ext g
  simp [map_mul, mul_apply_eq_comp]

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ V]
  [SMulCommClass ℝ 𝕜 V] [CompleteSpace V] in

private theorem orbitMap_comp_mulRight (h : G) (v : V) :
    (orbitMap π hπ v).comp (ContinuousMap.mulRight h) = orbitMap π hπ (π h v) := by
  ext g
  simp [map_mul, mul_apply_eq_comp]

@[simp]
theorem comp_haarAverageMap (h : G) :
    (π h).comp (haarAverageMap π hπ) = haarAverageMap π hπ := by
  ext v
  calc π h (haarAverageMap π hπ v)
      = haarAverage G (𝕜 := 𝕜) ((π h : C(V, V)).comp (orbitMap π hπ v)) := by
        rw [haarAverageMap_apply_eq_haarAverage, ContinuousLinearMap.haarAverage_comp_comm]
    _ = haarAverage G (𝕜 := 𝕜) (orbitMap π hπ v) := by
        rw [← orbitMap_comp_mulLeft, haarAverage_comp_mulLeft]
    _ = haarAverageMap π hπ v := (haarAverageMap_apply_eq_haarAverage π hπ v).symm

@[simp]
theorem comp_haarAverageMap_apply (h : G) (v : V) :
    π h (haarAverageMap π hπ v) = haarAverageMap π hπ v :=
  DFunLike.congr_fun (comp_haarAverageMap π hπ h) v

@[simp]
theorem haarAverageMap_comp (h : G) :
    (haarAverageMap π hπ).comp (π h) = haarAverageMap π hπ := by
  ext v
  calc haarAverageMap π hπ (π h v)
      = haarAverage G (𝕜 := 𝕜) ((orbitMap π hπ v).comp (ContinuousMap.mulRight h)) := by
        rw [orbitMap_comp_mulRight, haarAverageMap_apply_eq_haarAverage]
    _ = haarAverage G (𝕜 := 𝕜) (orbitMap π hπ v) := haarAverage_comp_mulRight G _ _
    _ = haarAverageMap π hπ v := (haarAverageMap_apply_eq_haarAverage π hπ v).symm

@[simp]
theorem haarAverageMap_comp_apply (h : G) (v : V) :
    haarAverageMap π hπ (π h v) = haarAverageMap π hπ v :=
  DFunLike.congr_fun (haarAverageMap_comp π hπ h) v

theorem haarAverageMap_invariant (v : V) : haarAverageMap π hπ v ∈ π.invariants :=
  fun h ↦ comp_haarAverageMap_apply π hπ h v

@[simp]
theorem haarAverageMap_id {v : V} (hv : v ∈ π.invariants) :
    haarAverageMap π hπ v = v := by
  have hconst : ∀ g : G, π g v = v := hv
  rw [haarAverageMap_apply]
  simp [hconst]

theorem isProj_haarAverageMap :
    LinearMap.IsProj π.invariants (haarAverageMap π hπ : V →ₗ[𝕜] V) where
  map_mem := haarAverageMap_invariant π hπ
  map_id _ hv := haarAverageMap_id π hπ hv

@[simp]
theorem haarAverageMap_comp_self :
    (haarAverageMap π hπ).comp (haarAverageMap π hπ) = haarAverageMap π hπ :=
  ContinuousLinearMap.coe_injective (isProj_haarAverageMap π hπ).isIdempotentElem

@[simp]
theorem range_haarAverageMap :
    LinearMap.range (haarAverageMap π hπ : V →ₗ[𝕜] V) = π.invariants :=
  (isProj_haarAverageMap π hπ).range

end Projection

section Trace

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

local instance instCompleteSpaceInvariants : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

theorem trace_haarAverageMap :
    LinearMap.trace 𝕜 V (haarAverageMap π hπ : V →ₗ[𝕜] V)
      = ∫ g, character π hπ g ∂haarProb G := by
  rw [haarAverageMap, trace_integratedOperator]
  simp

theorem integral_character_eq_finrank_invariants :
    ∫ g, character π hπ g ∂haarProb G = (Module.finrank 𝕜 π.invariants : 𝕜) := by
  rw [← trace_haarAverageMap π hπ, (isProj_haarAverageMap π hπ).trace]

theorem integral_character_eq_zero_iff :
    ∫ g, character π hπ g ∂haarProb G = 0 ↔ π.invariants = ⊥ := by
  rw [integral_character_eq_finrank_invariants π hπ, Nat.cast_eq_zero,
    Submodule.finrank_eq_zero]

end Trace

end ContRepresentation
