module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ContinuousAveraging
public import DedekindZetaZeroFree.RepresentationTheory.Compact.L2MatrixCoefficients
public import DedekindZetaZeroFree.RepresentationTheory.Continuous.HomRepresentation

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Compact/Intertwiner/Basic.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace DedekindZetaZeroFree.TauCeti

private theorem comp_inv_self {𝕜 G W : Type*} [RCLike 𝕜] [Group G]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W] (ρ : ContRepresentation 𝕜 G W) (g : G) :
    (ρ g).comp (ρ g⁻¹) = ContinuousLinearMap.id 𝕜 W := by
  rw [← ContinuousLinearMap.mul_def, ← map_mul, mul_inv_cancel, map_one]
  rfl

noncomputable def conjAction {𝕜 G V W : Type*} [RCLike 𝕜] [Group G]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W) (g : G) :
    (V →L[𝕜] W) →L[𝕜] V →L[𝕜] W :=
  ContRepresentation.linHom π ρ g⁻¹

private theorem conjAction_apply {𝕜 G V W : Type*} [RCLike 𝕜] [Group G]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W) (g : G) (S : V →L[𝕜] W) :
    conjAction π ρ g S = (ρ g⁻¹).comp (S.comp (π g)) := by
  rw [conjAction, ContRepresentation.linHom_apply, inv_inv]

end DedekindZetaZeroFree.TauCeti

open DedekindZetaZeroFree.TauCeti DedekindZetaZeroFree.TauCeti.ContRepresentation

namespace ContRepresentation

section CompactGroup

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
  (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ)

include hπ hρ

noncomputable def conjFamily (T : V →L[𝕜] W) : C(G, V →L[𝕜] W) where
  toFun g := (ρ g⁻¹).comp (T.comp (π g))
  continuous_toFun :=
    (hρ.comp continuous_inv).clm_comp (Continuous.clm_comp continuous_const hπ)

@[simp]
private theorem conjFamily_apply_apply (T : V →L[𝕜] W) (g : G) (v : V) :
    conjFamily π hπ ρ hρ T g v = ρ g⁻¹ (T (π g v)) :=
  rfl

private theorem conjAction_comp_conjFamily (T : V →L[𝕜] W) (g : G) :
    (conjAction π ρ g : C(V →L[𝕜] W, V →L[𝕜] W)).comp (conjFamily π hπ ρ hρ T)
      = (conjFamily π hπ ρ hρ T).comp (ContinuousMap.mulRight g) := by
  ext h v
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_coe, conjAction_apply,
    ContinuousLinearMap.comp_apply, conjFamily_apply_apply, ContinuousMap.coe_mulRight,
    mul_inv_rev, map_mul ρ, map_mul π, mul_apply_eq_comp]

variable [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]

noncomputable def averageOperator (T : V →L[𝕜] W) : V →L[𝕜] W :=
  haarAverage G (𝕜 := 𝕜) (conjFamily π hπ ρ hρ T)

@[simp]
theorem averageOperator_zero : averageOperator π hπ ρ hρ 0 = 0 := by
  have hzero : conjFamily π hπ ρ hρ 0 = 0 := by
    ext g v
    simp
  rw [averageOperator, hzero, map_zero]

@[simp]
theorem averageOperator_add (T₁ T₂ : V →L[𝕜] W) :
    averageOperator π hπ ρ hρ (T₁ + T₂)
      = averageOperator π hπ ρ hρ T₁ + averageOperator π hπ ρ hρ T₂ := by
  have hadd : conjFamily π hπ ρ hρ (T₁ + T₂)
      = conjFamily π hπ ρ hρ T₁ + conjFamily π hπ ρ hρ T₂ := by
    ext g v
    simp
  rw [averageOperator, averageOperator, averageOperator, hadd, map_add]

@[simp]
theorem averageOperator_smul (c : 𝕜) (T : V →L[𝕜] W) :
    averageOperator π hπ ρ hρ (c • T) = c • averageOperator π hπ ρ hρ T := by
  have hsmul : conjFamily π hπ ρ hρ (c • T) = c • conjFamily π hπ ρ hρ T := by
    ext g v
    simp
  rw [averageOperator, averageOperator, hsmul, map_smul]

variable [CompleteSpace W]

private theorem conjAction_averageOperator (T : V →L[𝕜] W) (g : G) :
    conjAction π ρ g (averageOperator π hπ ρ hρ T) = averageOperator π hπ ρ hρ T := by
  rw [averageOperator, ← ContinuousLinearMap.haarAverage_comp_comm,
    conjAction_comp_conjFamily π hπ ρ hρ T g, haarAverage_comp_mulRight]

theorem averageOperator_comp (T : V →L[𝕜] W) (g : G) : (averageOperator π hπ ρ hρ T).comp (π g)
      = (ρ g).comp (averageOperator π hπ ρ hρ T) := by
  have h := conjAction_averageOperator π hπ ρ hρ T g
  rw [conjAction_apply] at h
  calc (averageOperator π hπ ρ hρ T).comp (π g)
      = (ContinuousLinearMap.id 𝕜 W).comp ((averageOperator π hπ ρ hρ T).comp (π g)) := by
        rw [ContinuousLinearMap.id_comp]
    _ = ((ρ g).comp (ρ g⁻¹)).comp ((averageOperator π hπ ρ hρ T).comp (π g)) := by
        rw [comp_inv_self ρ g]
    _ = (ρ g).comp ((ρ g⁻¹).comp ((averageOperator π hπ ρ hρ T).comp (π g))) :=
        ContinuousLinearMap.comp_assoc _ _ _
    _ = (ρ g).comp (averageOperator π hπ ρ hρ T) := by rw [h]

noncomputable def averageIntertwiner (T : V →L[𝕜] W) : ContIntertwiningMap π ρ where
  __ := averageOperator π hπ ρ hρ T
  isIntertwining' g := averageOperator_comp π hπ ρ hρ T g

@[simp]
theorem toContinuousLinearMap_averageIntertwiner (T : V →L[𝕜] W) :
    (averageIntertwiner π hπ ρ hρ T).toContinuousLinearMap = averageOperator π hπ ρ hρ T :=
  (rfl)

@[simp]
theorem averageIntertwiner_apply (T : V →L[𝕜] W) (v : V) :
    averageIntertwiner π hπ ρ hρ T v = averageOperator π hπ ρ hρ T v :=
  (rfl)

theorem averageOperator_eq_self (T : V →L[𝕜] W) (hT : ∀ g : G, T.comp (π g) = (ρ g).comp T) :
    averageOperator π hπ ρ hρ T = T := by
  have hT_apply (g : G) (v : V) : T (π g v) = ρ g (T v) :=
    congrArg (fun S : V →L[𝕜] W ↦ S v) (hT g)
  have hconst : conjFamily π hπ ρ hρ T = ContinuousMap.const G T := by
    ext g v
    rw [conjFamily_apply_apply, hT_apply g v]
    exact Representation.inv_self_apply ρ.toRepresentation g (T v)
  rw [averageOperator, hconst, haarAverage_const]

@[simp]
theorem averageOperator_toContinuousLinearMap (f : ContIntertwiningMap π ρ) :
    averageOperator π hπ ρ hρ f.toContinuousLinearMap = f.toContinuousLinearMap :=
  averageOperator_eq_self π hπ ρ hρ _ f.isIntertwining'

@[simp]
theorem averageOperator_averageOperator (T : V →L[𝕜] W) :
    averageOperator π hπ ρ hρ (averageOperator π hπ ρ hρ T) = averageOperator π hπ ρ hρ T :=
  averageOperator_eq_self π hπ ρ hρ _ (averageOperator_comp π hπ ρ hρ T)

end CompactGroup

section SelfAverage

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [CompleteSpace V]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

@[simp]
theorem averageOperator_id :
    averageOperator π hπ π hπ (ContinuousLinearMap.id 𝕜 V) = ContinuousLinearMap.id 𝕜 V :=
  averageOperator_eq_self π hπ π hπ _ fun g ↦ by
    rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

end SelfAverage

section Trace

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

private theorem trace_conjFamily (T : V →L[𝕜] V) (g : G) :
    LinearMap.trace 𝕜 V (conjFamily π hπ π hπ T g : V →ₗ[𝕜] V)
      = LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V) := by
  have hconj : ((conjFamily π hπ π hπ T g : V →L[𝕜] V) : V →ₗ[𝕜] V)
      = ↑(π.toRepresentation.asGroupHom g⁻¹) * (T : V →ₗ[𝕜] V)
        * ↑(π.toRepresentation.asGroupHom g⁻¹)⁻¹ := by
    ext v
    simp [← map_inv, Representation.asGroupHom_apply,
      ContRepresentation.toMonoidHom_apply]
  rw [hconj, LinearMap.trace_conj]

variable [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

local instance completeSpace_of_finiteDimensional : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

theorem trace_averageOperator (T : V →L[𝕜] V) :
    LinearMap.trace 𝕜 V (averageOperator π hπ π hπ T : V →ₗ[𝕜] V)
      = LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V) := by
  have hconst : (traceCLM 𝕜 V : C(V →L[𝕜] V, 𝕜)).comp (conjFamily π hπ π hπ T)
      = ContinuousMap.const G (LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V)) :=
    ContinuousMap.ext fun g ↦ by
      rw [ContinuousMap.comp_apply]
      exact (traceCLM_apply _).trans (trace_conjFamily π hπ T g)
  have h := (traceCLM 𝕜 V).haarAverage_comp_comm (G := G) (conjFamily π hπ π hπ T)
  rw [hconst, haarAverage_const] at h
  rw [← traceCLM_apply, averageOperator, ← h]

end Trace

section Orthogonality

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [CompleteSpace W]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
  (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ)

include hπ hρ

theorem inner_averageOperator (T : V →L[𝕜] W) (v : V) (w : W) :
    ⟪w, averageOperator π hπ ρ hρ T v⟫_𝕜 = ∫ g, ⟪w, ρ g⁻¹ (T (π g v))⟫_𝕜 ∂haarProb G := by
  have h := ((innerSL 𝕜 w).comp (ContinuousLinearMap.apply 𝕜 W v)).haarAverage_comp_comm
    (G := G) (conjFamily π hπ ρ hρ T)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at h
  rw [averageOperator, ← innerSL_apply_apply, ← h, haarAverage_apply]
  rfl

theorem inner_averageOperator_of_isUnitary (hunitary : IsUnitary ρ) (T : V →L[𝕜] W)
    (v : V) (w : W) :
    ⟪w, averageOperator π hπ ρ hρ T v⟫_𝕜 = ∫ g, ⟪ρ g w, T (π g v)⟫_𝕜 ∂haarProb G := by
  rw [inner_averageOperator π hπ ρ hρ T v w]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)

  beta_reduce
  rw [hunitary.inner_map_right g⁻¹ w (T (π g v)), inv_inv]

theorem inner_matrixCoeffLp_eq_inner_averageOperator (hunitary : IsUnitary ρ)
    (v w : V) (v' w' : W) :
    ⟪matrixCoeffLp π hπ v w, matrixCoeffLp ρ hρ v' w'⟫_𝕜
      = ⟪v', averageOperator π hπ ρ hρ (InnerProductSpace.rankOne 𝕜 w' w) v⟫_𝕜 := by
  rw [inner_matrixCoeffLp π hπ ρ hρ v w v' w',
    inner_averageOperator_of_isUnitary π hπ ρ hρ hunitary _ v v']
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)

  beta_reduce
  rw [InnerProductSpace.inner_right_rankOne_apply, inner_conj_symm w (π g v)]

theorem schur_orthogonality_distinct (hunitary : IsUnitary ρ)
    (hdistinct : ∀ f : ContIntertwiningMap π ρ, f.toContinuousLinearMap = 0) (v w : V) (v' w' : W) :
    ⟪matrixCoeffLp π hπ v w, matrixCoeffLp ρ hρ v' w'⟫_𝕜 = 0 := by
  have hzero : averageOperator π hπ ρ hρ (InnerProductSpace.rankOne 𝕜 w' w) = 0 := by
    simpa using hdistinct (averageIntertwiner π hπ ρ hρ (InnerProductSpace.rankOne 𝕜 w' w))
  rw [inner_matrixCoeffLp_eq_inner_averageOperator π hπ ρ hρ hunitary v w v' w', hzero]
  simp

end Orthogonality

end ContRepresentation
