module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Herbrand.FamilyCardinality
public import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.EquivariantEquiv

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Transport from local blocks to unrestricted factors

This leaf transports the finite-family Herbrand calculation to the actual
unrestricted relative S-idele factors.
-/

open scoped NumberField BigOperators ValuativeRel Classical NNReal
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-!
## Canonical factor-transport action providers
-/

omit [NumberField L] in
@[reducible]
 noncomputable def
    relativeUnrestrictedSPlaceFactorsActionProvider
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeUnrestrictedSPlaceFactors
        (K := K) (L := L) S) :=
  relativeUnrestrictedSPlaceFactorsAction
    (K := K) (L := L) S

omit [NumberField L] in
@[reducible]
 noncomputable def
    relativeUnrestrictedSPlaceLocalBlockFamilyActionProvider
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (LocalBlockFamily
        (relativeUnrestrictedSPlaceDatum
          (K := K) (L := L) S)) :=
  localBlockFamilyAction
    (relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S)

omit [NumberField L] in
/-- The equivariant realization by local blocks identifies degree-zero
Herbrand cohomology of the actual unrestricted factors with that of the
local-block family. -/
noncomputable def
    relativeUnrestrictedSPlaceFactorsHerbrandH0EquivLocalBlockFamily
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    @HerbrandH0 (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S)
        _ _ _
        (relativeUnrestrictedSPlaceFactorsAction
          (K := K) (L := L) S) ≃*
      @HerbrandH0 (L ≃ₐ[K] L)
        (LocalBlockFamily
          (relativeUnrestrictedSPlaceDatum
            (K := K) (L := L) S))
        _ _ _
        (localBlockFamilyAction
          (relativeUnrestrictedSPlaceDatum
            (K := K) (L := L) S)) := by
  let d :=
    relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S
  letI sourceAction :=
    relativeUnrestrictedSPlaceFactorsActionProvider
      (K := K) (L := L) S
  letI targetAction :=
    relativeUnrestrictedSPlaceLocalBlockFamilyActionProvider
      (K := K) (L := L) S
  exact
    herbrandH0EquivariantMulEquiv
      (relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily
        (K := K) (L := L) S)
      (relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily_smul
        (K := K) (L := L) S)

omit [NumberField L] in
/-- The equivariant realization by local blocks identifies degree-minus-one
Herbrand cohomology of the actual unrestricted factors with that of the
local-block family. -/
noncomputable def
    relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneEquivLocalBlockFamily
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L) :
    @HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S)
        _ _ _
        (relativeUnrestrictedSPlaceFactorsAction
          (K := K) (L := L) S) σ ≃*
      @HerbrandHMinusOne (L ≃ₐ[K] L)
        (LocalBlockFamily
          (relativeUnrestrictedSPlaceDatum
            (K := K) (L := L) S))
        _ _ _
        (localBlockFamilyAction
          (relativeUnrestrictedSPlaceDatum
            (K := K) (L := L) S)) σ := by
  let d :=
    relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S
  letI sourceAction :=
    relativeUnrestrictedSPlaceFactorsActionProvider
      (K := K) (L := L) S
  letI targetAction :=
    relativeUnrestrictedSPlaceLocalBlockFamilyActionProvider
      (K := K) (L := L) S
  exact
    herbrandHMinusOneEquivariantMulEquiv
      (relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily
        (K := K) (L := L) S)
      (relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily_smul
        (K := K) (L := L) S) σ

omit [NumberField L] in
/-- Degree-zero cohomology of the actual unrestricted tensor factors is
finite. -/
theorem relativeUnrestrictedSPlaceFactorsHerbrandH0Finite
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI :=
      relativeUnrestrictedSPlaceFactorsAction
        (K := K) (L := L) S
    Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S)) := by
  -- Take the finiteness statement with its own `let`s reduced, so that it
  -- states finiteness for the explicit datum; comparing it against a
  -- separately introduced `let d` would unfold the completions.
  have targetFinite :=
    relativeUnrestrictedLocalBlockFamilyHerbrandH0Finite
      (K := K) (L := L) S σ hgen
  dsimp only at targetFinite
  exact
    Finite.of_equiv _
      (relativeUnrestrictedSPlaceFactorsHerbrandH0EquivLocalBlockFamily
        (K := K) (L := L) S).symm.toEquiv

omit [NumberField L] in
/-- Degree-minus-one cohomology of the actual unrestricted tensor
factors is finite. -/
theorem relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI :=
      relativeUnrestrictedSPlaceFactorsAction
        (K := K) (L := L) S
    Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S) σ) := by
  -- Take the finiteness statement with its own `let`s reduced, so that it
  -- states finiteness for the explicit datum; comparing it against a
  -- separately introduced `let d` would unfold the completions.
  have targetFinite :=
    relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOneFinite
      (K := K) (L := L) S σ hgen
  dsimp only at targetFinite
  exact
    Finite.of_equiv _
      (relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneEquivLocalBlockFamily
        (K := K) (L := L) S σ).symm.toEquiv

omit [NumberField L] in
/-- Degree zero for the actual unrestricted factors: its
cardinality is the product of the local degrees. -/
theorem
    relativeUnrestrictedSPlaceFactorsHerbrandH0_card_eq_product
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI :=
      relativeUnrestrictedSPlaceFactorsAction
        (K := K) (L := L) S
    letI : Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S)) :=
      relativeUnrestrictedSPlaceFactorsHerbrandH0Finite
        S σ hgen
    Nat.card
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S)) =
      ∏ i,
        relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i := by
  have hcard :=
    relativeUnrestrictedLocalBlockFamilyHerbrandH0_card_eq_product
      (K := K) (L := L) S σ hgen
  exact
    (Nat.card_congr
      (relativeUnrestrictedSPlaceFactorsHerbrandH0EquivLocalBlockFamily
        (K := K) (L := L) S).toEquiv).trans hcard

omit [NumberField L] in
/-- Degree minus one for the actual unrestricted factors:
the group has one element. -/
theorem
    relativeUnrestrictedSPlaceFactorsHerbrandHMinusOne_card_eq_one
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI :=
      relativeUnrestrictedSPlaceFactorsAction
        (K := K) (L := L) S
    letI : Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S) σ) :=
      relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite
        S σ hgen
    Nat.card
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S) σ) = 1 := by
  have hcard :=
    relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOne_card_eq_one
      (K := K) (L := L) S σ hgen
  exact
    (Nat.card_congr
      (relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneEquivLocalBlockFamily
        (K := K) (L := L) S σ).toEquiv).trans hcard

omit [NumberField L] in
/-- The Herbrand quotient formula for the actual unrestricted tensor factors. -/
theorem relativeUnrestrictedSPlaceFactors_herbrandQuotient
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI :=
      relativeUnrestrictedSPlaceFactorsAction
        (K := K) (L := L) S
    letI : Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S)) :=
      relativeUnrestrictedSPlaceFactorsHerbrandH0Finite
        S σ hgen
    letI : Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S) σ) :=
      relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite
        S σ hgen
    herbrandQuotient
        (G := L ≃ₐ[K] L)
        (A := RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S) σ =
      ∏ i,
        (relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i : ℚ) := by
  let :=
    relativeUnrestrictedSPlaceFactorsAction
      (K := K) (L := L) S
  let : Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S)) :=
    relativeUnrestrictedSPlaceFactorsHerbrandH0Finite
      S σ hgen
  let : Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S) σ) :=
    relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite
      S σ hgen
  rw [herbrandQuotient_eq_card_ratio,
    relativeUnrestrictedSPlaceFactorsHerbrandH0_card_eq_product
      S σ hgen,
    relativeUnrestrictedSPlaceFactorsHerbrandHMinusOne_card_eq_one
      S σ hgen]
  simp only [Nat.cast_prod, Nat.cast_one, div_one]

end
