module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Herbrand.FamilyFinite

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Cardinalities of finite unrestricted local-block families

This leaf computes the two finite-family Herbrand cardinalities from the
finiteness results and the canonical family instance providers.
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

omit [NumberField L] in
/-- The degree-zero cardinality of the unrestricted local-block family
is the product of its local degrees. -/
theorem
    relativeUnrestrictedLocalBlockFamilyHerbrandH0_card_eq_product
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI : ∀ i, MulDistribMulAction
        (absoluteValueDecompositionGroup K ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension.1)
        (LocalizedCompletion
          ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension)ˣ :=
      fun i =>
        decompositionGroupLocalUnitsAction
          ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base_isNontrivial
          ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension
    letI : ∀ i, MulDistribMulAction
        (L ≃ₐ[K] L)
        (LocalPlaceBlock
          ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base_isNontrivial
          ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension) :=
      fun i =>
        inducedMulDistribMulAction
          (absoluteValueDecompositionGroup K
            ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension.1)
    letI : MulDistribMulAction (L ≃ₐ[K] L)
        (LocalBlockFamily (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S)) :=
      piMulDistribMulAction (L ≃ₐ[K] L)
        (fun i =>
          LocalPlaceBlock
            ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base_isNontrivial
            ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension)
    letI : Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (LocalBlockFamily (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S))) :=
      relativeUnrestrictedLocalBlockFamilyHerbrandH0Finite
        S σ hgen
    Nat.card
        (HerbrandH0 (L ≃ₐ[K] L)
          (LocalBlockFamily (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S))) =
      ∏ i,
        relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i := by
  let localAction :=
    localBlockFamilyLocalAction (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S)
  let blockAction :=
    localBlockFamilyBlockAction (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S)
  let familyAction :=
    localBlockFamilyAction (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S)
  let decompositionFintype :=
    localBlockFamilyDecompositionFintype (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S)
  let localFinite : ∀ i, Finite
      (HerbrandH0
        (absoluteValueDecompositionGroup K ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension.1)
        (LocalizedCompletion
          ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension)ˣ) :=
    fun i =>
      relativeUnrestrictedLocalHerbrandH0Finite
        S i σ hgen
  let familyFinite : Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (LocalBlockFamily (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S))) :=
    relativeUnrestrictedLocalBlockFamilyHerbrandH0Finite
      S σ hgen
  calc
    Nat.card
        (HerbrandH0 (L ≃ₐ[K] L)
          (LocalBlockFamily (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S))) =
      Nat.card
        (∀ i,
          HerbrandH0
            (absoluteValueDecompositionGroup K
              ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension.1)
            (LocalizedCompletion
              ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension)ˣ) :=
      Nat.card_congr
        (localBlockFamilyHerbrandH0Equiv
          (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) σ hgen).toEquiv
    _ = ∏ i, Nat.card
        (HerbrandH0
          (absoluteValueDecompositionGroup K
            ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension.1)
          (LocalizedCompletion
            ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension)ˣ) :=
      Nat.card_pi
    _ = ∏ i,
        relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i := by
      apply Finset.prod_congr rfl
      intro i _
      exact
        relativeUnrestrictedLocalHerbrandH0_card_eq_localDegree
          S i σ hgen

omit [NumberField L] in
/-- The degree-minus-one cardinality of the unrestricted local-block
family is one. -/
theorem
    relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOne_card_eq_one
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI : ∀ i, MulDistribMulAction
        (absoluteValueDecompositionGroup K ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension.1)
        (LocalizedCompletion
          ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension)ˣ :=
      fun i =>
        decompositionGroupLocalUnitsAction
          ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base_isNontrivial
          ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension
    letI : ∀ i, MulDistribMulAction
        (L ≃ₐ[K] L)
        (LocalPlaceBlock
          ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base_isNontrivial
          ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension) :=
      fun i =>
        inducedMulDistribMulAction
          (absoluteValueDecompositionGroup K
            ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension.1)
    letI : MulDistribMulAction (L ≃ₐ[K] L)
        (LocalBlockFamily (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S)) :=
      piMulDistribMulAction (L ≃ₐ[K] L)
        (fun i =>
          LocalPlaceBlock
            ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base_isNontrivial
            ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension)
    letI : Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (LocalBlockFamily (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S)) σ) :=
      relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOneFinite
        S σ hgen
    Nat.card
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (LocalBlockFamily (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S)) σ) = 1 := by
  let localAction :=
    localBlockFamilyLocalAction (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S)
  let blockAction :=
    localBlockFamilyBlockAction (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S)
  let familyAction :=
    localBlockFamilyAction (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S)
  let decompositionFintype :=
    localBlockFamilyDecompositionFintype (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S)
  let localFinite : ∀ i, Finite
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension.1)
        (LocalizedCompletion
          ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K
            ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension.1)
          σ hgen)) :=
    fun i =>
      relativeUnrestrictedLocalHerbrandHMinusOneFinite
        S i σ hgen
  let familyFinite : Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (LocalBlockFamily (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S)) σ) :=
    relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOneFinite
      S σ hgen
  calc
    Nat.card
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (LocalBlockFamily (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S)) σ) =
      Nat.card
        (∀ i,
          HerbrandHMinusOne
            (absoluteValueDecompositionGroup K
              ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension.1)
            (LocalizedCompletion
              ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension)ˣ
            (subgroupGeneratorOfGenerator
              (absoluteValueDecompositionGroup K
                ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension.1)
              σ hgen)) :=
      Nat.card_congr
        (localBlockFamilyHerbrandHMinusOneEquiv
          (relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) σ hgen).toEquiv
    _ = ∏ i, Nat.card
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K
            ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension.1)
          (LocalizedCompletion
            ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).base ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K
              ((relativeUnrestrictedSPlaceDatum (K := K) (L := L) S) i).extension.1)
            σ hgen)) :=
      Nat.card_pi
    _ = ∏ _i :
        RelativeUnrestrictedSPlaceIndex (K := K) S, 1 := by
      apply Finset.prod_congr rfl
      intro i _
      exact
        relativeUnrestrictedLocalHerbrandHMinusOne_card_eq_one
          S i σ hgen
    _ = 1 := by simp

end
