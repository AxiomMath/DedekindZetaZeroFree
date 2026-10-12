module

public import DedekindZetaZeroFree.RepresentationTheory.Compact.AveragedIntertwiners
public import DedekindZetaZeroFree.RepresentationTheory.Continuous.SchurLemma
public import DedekindZetaZeroFree.RepresentationTheory.Irreducible.SubrepresentationsAndEigenvectors

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Compact/SchurOrthogonality.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open MeasureTheory
open scoped InnerProductSpace
open scoped MonoidAlgebra

open DedekindZetaZeroFree.TauCeti DedekindZetaZeroFree.TauCeti.ContRepresentation

namespace ContRepresentation

section Average

variable {𝕜 G V : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

local instance instCompleteSpaceSchurAverage : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

theorem averageOperator_eq_finrank_inv_mul_trace_smul_id
    (hirr : Representation.IsIrreducible π.toRepresentation) (T : V →L[𝕜] V) :
    averageOperator π hπ π hπ T =
      ((Module.finrank 𝕜 V : 𝕜)⁻¹ * LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V)) •
        ContinuousLinearMap.id 𝕜 V := by
  have hdim : (Module.finrank 𝕜 V : 𝕜) ≠ 0 :=
    Representation.IsIrreducible.natCast_finrank_ne_zero hirr
  have h := π.eq_finrank_inv_mul_trace_smul_id_of_isIrreducible hdim hirr
    (averageIntertwiner π hπ π hπ T)
  rwa [toContinuousLinearMap_averageIntertwiner, trace_averageOperator] at h

end Average

section Orthogonality

variable {𝕜 G V : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

local instance instCompleteSpaceSchurOrthogonality : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

theorem schur_orthogonality_self (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) (v₁ w₁ v₂ w₂ : V) :
    ⟪matrixCoeffLp π hπ v₁ w₁, matrixCoeffLp π hπ v₂ w₂⟫_𝕜 =
      (Module.finrank 𝕜 V : 𝕜)⁻¹ *
        ((starRingEnd 𝕜) ⟪v₁, v₂⟫_𝕜 * ⟪w₁, w₂⟫_𝕜) := by
  rw [inner_matrixCoeffLp_eq_inner_averageOperator π hπ π hπ hunitary,
    averageOperator_eq_finrank_inv_mul_trace_smul_id π hπ hirr,
    smul_apply, ContinuousLinearMap.id_apply, InnerProductSpace.trace_rankOne, inner_smul_right]
  rw [← inner_conj_symm v₂ v₁]
  ring

theorem schur_orthogonality_basis (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation)
    {d : ℕ} (e : OrthonormalBasis (Fin d) 𝕜 V) (i j k l : Fin d) :
    ⟪matrixCoeffLp π hπ (e j) (e i), matrixCoeffLp π hπ (e l) (e k)⟫_𝕜 =
      (d : 𝕜)⁻¹ *
        ((if j = l then (1 : 𝕜) else 0) * (if i = k then (1 : 𝕜) else 0)) := by
  rw [schur_orthogonality_self π hπ hunitary hirr]
  rw [Module.finrank_eq_card_basis e.toBasis, Fintype.card_fin]
  simp only [orthonormal_iff_ite.mp e.orthonormal]
  split_ifs <;> simp_all

end Orthogonality

end ContRepresentation
