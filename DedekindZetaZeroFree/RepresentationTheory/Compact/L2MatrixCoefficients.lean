module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LpClassFunctions
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactProbabilityMeasure
public import DedekindZetaZeroFree.RepresentationTheory.Continuous.MatrixCoefficients
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Compact/MatrixCoefficient.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace DedekindZetaZeroFree.TauCeti

namespace ContRepresentation

section CompactGroup

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

noncomputable def matrixCoeffLp (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w : V) : Lp 𝕜 2 (haarProb G) :=
  ContinuousMap.toLp 2 (haarProb G) 𝕜 (matrixCoeff π hπ v w)

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

theorem matrixCoeffLp_def (v w : V) :
    matrixCoeffLp π hπ v w = ContinuousMap.toLp 2 (haarProb G) 𝕜 (matrixCoeff π hπ v w) :=
  (rfl)

@[simp]
theorem matrixCoeffLp_zero_left (w : V) : matrixCoeffLp π hπ 0 w = 0 := by
  simp [matrixCoeffLp_def]

@[simp]
theorem matrixCoeffLp_zero_right (v : V) : matrixCoeffLp π hπ v 0 = 0 := by
  simp [matrixCoeffLp_def]

@[simp]
theorem matrixCoeffLp_add_left (v₁ v₂ w : V) :
    matrixCoeffLp π hπ (v₁ + v₂) w = matrixCoeffLp π hπ v₁ w + matrixCoeffLp π hπ v₂ w := by
  simp [matrixCoeffLp_def]

@[simp]
theorem matrixCoeffLp_add_right (v w₁ w₂ : V) :
    matrixCoeffLp π hπ v (w₁ + w₂) = matrixCoeffLp π hπ v w₁ + matrixCoeffLp π hπ v w₂ := by
  simp [matrixCoeffLp_def]

@[simp]
theorem matrixCoeffLp_smul_left (c : 𝕜) (v w : V) :
    matrixCoeffLp π hπ (c • v) w = (starRingEnd 𝕜) c • matrixCoeffLp π hπ v w := by
  simp [matrixCoeffLp_def]

@[simp]
theorem matrixCoeffLp_smul_right (v : V) (c : 𝕜) (w : V) :
    matrixCoeffLp π hπ v (c • w) = c • matrixCoeffLp π hπ v w := by
  simp [matrixCoeffLp_def]

theorem inner_matrixCoeffLp (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ) (v w : V)
    (v' w' : W) :
    ⟪matrixCoeffLp π hπ v w, matrixCoeffLp ρ hρ v' w'⟫_𝕜
      = ∫ g, ⟪ρ g v', w'⟫_𝕜 * (starRingEnd 𝕜) ⟪π g v, w⟫_𝕜 ∂(haarProb G) := by
  rw [matrixCoeffLp_def, matrixCoeffLp_def, ContinuousMap.inner_toLp]
  simp

end CompactGroup

end ContRepresentation

end DedekindZetaZeroFree.TauCeti
