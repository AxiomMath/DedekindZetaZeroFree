module

public import DedekindZetaZeroFree.RepresentationTheory.Compact.SchurOrthogonality

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Compact/Character/Basic.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open MeasureTheory
open scoped InnerProductSpace

open DedekindZetaZeroFree.TauCeti DedekindZetaZeroFree.TauCeti.ContRepresentation

namespace ContRepresentation

section CharacterLp

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

noncomputable def characterLp (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    Lp 𝕜 2 (haarProb G) :=
  ContinuousMap.toLp 2 (haarProb G) 𝕜 (character π hπ)

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

theorem characterLp_def :
    characterLp π hπ = ContinuousMap.toLp 2 (haarProb G) 𝕜 (character π hπ) :=
  (rfl)

end CharacterLp

section CompactGroup

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

theorem inner_characterLp_eq_sum (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : OrthonormalBasis ι 𝕜 V)
    (f : OrthonormalBasis κ 𝕜 W) :
    ⟪characterLp π hπ, characterLp ρ hρ⟫_𝕜 =
      ∑ i, ∑ k, ⟪matrixCoeffLp ρ hρ (f k) (f k), matrixCoeffLp π hπ (e i) (e i)⟫_𝕜 := by

  have hstar :
      ⟪ContinuousMap.toLp 2 (haarProb G) 𝕜 (star (character ρ hρ)),
        ContinuousMap.toLp 2 (haarProb G) 𝕜 (star (character π hπ))⟫_𝕜 =
      ⟪characterLp π hπ, characterLp ρ hρ⟫_𝕜 := by
    simp [characterLp_def, ContinuousMap.inner_toLp, mul_comm]
  rw [star_character ρ hρ f, star_character π hπ e, map_sum, map_sum] at hstar
  simp only [← matrixCoeffLp_def, sum_inner, inner_sum] at hstar
  rw [← hstar, Finset.sum_comm]

end CompactGroup

section Orthogonality

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [FiniteDimensional 𝕜 W]

local instance instCompleteSpaceCharacterDomain : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

local instance instCompleteSpaceCharacterCodomain : CompleteSpace W :=
  FiniteDimensional.complete 𝕜 W

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

theorem character_orthonormal_self [IsAlgClosed 𝕜] (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    ⟪characterLp π hπ, characterLp π hπ⟫_𝕜 = 1 := by
  classical
  let : Representation.IsIrreducible π.toRepresentation := hirr
  have hd : (Module.finrank 𝕜 V : 𝕜) ≠ 0 :=
    Representation.IsIrreducible.natCast_finrank_ne_zero hirr
  set e := stdOrthonormalBasis 𝕜 V

  have hrow : ∀ i, ∑ k, ⟪matrixCoeffLp π hπ (e k) (e k), matrixCoeffLp π hπ (e i) (e i)⟫_𝕜 =
      (Module.finrank 𝕜 V : 𝕜)⁻¹ := by
    intro i
    simp only [π.schur_orthogonality_basis hπ hunitary hirr e]
    rw [Finset.sum_eq_single i (fun k _ hk ↦ by simp [hk]) (by simp)]
    simp
  rw [inner_characterLp_eq_sum π hπ π hπ e e, Finset.sum_congr rfl fun i _ ↦ hrow i,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hd]

omit [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W] in

theorem character_orthonormal_distinct (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ)
    (hunitary : IsUnitary π)
    (hdistinct : ∀ f : ContIntertwiningMap ρ π, f.toContinuousLinearMap = 0) :
    ⟪characterLp π hπ, characterLp ρ hρ⟫_𝕜 = 0 := by
  rw [inner_characterLp_eq_sum π hπ ρ hρ (stdOrthonormalBasis 𝕜 V) (stdOrthonormalBasis 𝕜 W)]
  simp [schur_orthogonality_distinct ρ hρ π hπ hunitary hdistinct]

end Orthogonality

end ContRepresentation
