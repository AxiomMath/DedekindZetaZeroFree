module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ContinuousAveraging
public import DedekindZetaZeroFree.RepresentationTheory.Continuous.UnitaryActions
public import Mathlib.Analysis.InnerProductSpace.Positive

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Compact/Unitarizable.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open MeasureTheory RCLike DedekindZetaZeroFree.TauCeti
open scoped InnerProductSpace

namespace ContRepresentation

section NormedField

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [Group G] [TopologicalSpace G]
  [CompactSpace G] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

theorem exists_pos_mul_norm_le_norm_map (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    ∃ c : ℝ, 0 < c ∧ ∀ (g : G) (v : V), c * ‖v‖ ≤ ‖π g v‖ := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn (f := fun g : G ↦ π g)
    hπ.continuousOn
  set M' := max M 1
  have hM'pos : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨M'⁻¹, inv_pos.mpr hM'pos, fun g v ↦ ?_⟩
  have hcancel : π g⁻¹ (π g v) = v := Representation.inv_self_apply π.toRepresentation g v
  have hstep : ‖v‖ ≤ M' * ‖π g v‖ :=
    calc ‖v‖ = ‖π g⁻¹ (π g v)‖ := by rw [hcancel]
      _ ≤ ‖π g⁻¹‖ * ‖π g v‖ := (π g⁻¹).le_opNorm _
      _ ≤ M' * ‖π g v‖ :=
        mul_le_mul_of_nonneg_right ((hM g⁻¹ (Set.mem_univ _)).trans (le_max_left _ _))
          (norm_nonneg _)
  rw [inv_mul_le_iff₀ hM'pos]
  exact hstep

end NormedField

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

noncomputable def gramFamily : C(G, V →L[𝕜] V) where
  toFun g := (ContinuousLinearMap.adjoint (π g)).comp (π g)
  continuous_toFun :=
    (ContinuousLinearMap.compL 𝕜 V V V).continuous₂.comp
      (((ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := V) (F := V)).continuous.comp hπ).prodMk hπ)

noncomputable def gramOperator : V →L[𝕜] V :=
  letI := NormedSpace.restrictScalars ℝ 𝕜 V
  letI := IsScalarTower.restrictScalars ℝ 𝕜 V
  haarAverage G (𝕜 := 𝕜) (gramFamily π hπ)

theorem inner_gramOperator (v w : V) :
    ⟪v, gramOperator π hπ w⟫_𝕜 = ∫ g, ⟪π g v, π g w⟫_𝕜 ∂haarProb G := by
  let := NormedSpace.restrictScalars ℝ 𝕜 V
  let := IsScalarTower.restrictScalars ℝ 𝕜 V
  have h := ((innerSL 𝕜 v).comp (ContinuousLinearMap.apply 𝕜 V w)).haarAverage_comp_comm
    (G := G) (gramFamily π hπ)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at h
  rw [gramOperator, ← innerSL_apply_apply, ← h, haarAverage_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  rw [ContinuousMap.comp_apply]
  dsimp [gramFamily]
  exact ContinuousLinearMap.adjoint_inner_right (π g) v (π g w)

theorem inner_gramOperator_left (v w : V) :
    ⟪gramOperator π hπ v, w⟫_𝕜 = ∫ g, ⟪π g v, π g w⟫_𝕜 ∂haarProb G := by
  rw [← inner_conj_symm, inner_gramOperator, ← integral_conj]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g ↦ inner_conj_symm _ _)

theorem isSymmetric_gramOperator : (gramOperator π hπ : V →ₗ[𝕜] V).IsSymmetric := fun v w ↦ by
  simp only [ContinuousLinearMap.coe_coe]
  rw [inner_gramOperator_left, inner_gramOperator]

omit [CompleteSpace V] in

private theorem integrable_norm_sq (v : V) :
    Integrable (fun g ↦ ‖π g v‖ ^ 2) (haarProb G) :=
  ((continuous_norm.comp (hπ.clm_apply continuous_const)).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem inner_gramOperator_self (v : V) :
    ⟪gramOperator π hπ v, v⟫_𝕜 = ((∫ g, ‖π g v‖ ^ 2 ∂haarProb G : ℝ) : 𝕜) := by
  rw [inner_gramOperator_left, ← integral_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  simp [inner_self_eq_norm_sq_to_K]

theorem exists_pos_mul_norm_sq_le_re_inner_gramOperator :
    ∃ c : ℝ, 0 < c ∧ ∀ v : V, c * ‖v‖ ^ 2 ≤ re ⟪gramOperator π hπ v, v⟫_𝕜 := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_mul_norm_le_norm_map π hπ
  refine ⟨c ^ 2, sq_pos_of_pos hc, fun v ↦ ?_⟩
  rw [inner_gramOperator_self, ofReal_re, ← mul_pow]
  have h := integral_mono (integrable_const ((c * ‖v‖) ^ 2)) (integrable_norm_sq π hπ v)
    fun g ↦ pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg v)) (hbound g v) 2
  simpa using h

theorem re_inner_gramOperator_self_pos {v : V} (hv : v ≠ 0) :
    0 < re ⟪gramOperator π hπ v, v⟫_𝕜 := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_mul_norm_sq_le_re_inner_gramOperator π hπ
  exact (mul_pos hc (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).trans_le (hbound v)

@[simp]
theorem inner_gramOperator_map_map (g : G) (v w : V) :
    ⟪π g v, gramOperator π hπ (π g w)⟫_𝕜 = ⟪v, gramOperator π hπ w⟫_𝕜 := by
  rw [inner_gramOperator, inner_gramOperator]
  simpa only [map_mul, mul_apply_eq_comp] using
    integral_mul_right_eq_self (μ := haarProb G) (fun h ↦ ⟪π h v, π h w⟫_𝕜) g

@[simp]
theorem adjoint_comp_gramOperator_comp (g : G) :
    (ContinuousLinearMap.adjoint (π g)).comp ((gramOperator π hπ).comp (π g)) =
      gramOperator π hπ := by
  ext w
  apply ext_inner_left 𝕜
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_gramOperator_map_map]

@[simp]
theorem gramOperator_eq_one (hunitary : DedekindZetaZeroFree.TauCeti.ContRepresentation.IsUnitary π) :
    gramOperator π hπ = 1 := by
  let := NormedSpace.restrictScalars ℝ 𝕜 V
  let := IsScalarTower.restrictScalars ℝ 𝕜 V
  have hconst : gramFamily π hπ = ContinuousMap.const G 1 :=
    ContinuousMap.ext fun g ↦ hunitary.adjoint_comp_self g
  rw [gramOperator, hconst, haarAverage_const]

end ContRepresentation
