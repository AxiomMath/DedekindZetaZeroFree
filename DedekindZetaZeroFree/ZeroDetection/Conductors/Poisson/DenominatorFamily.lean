module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyCount
public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.LocalTypeCover
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AllIdealTransfer
public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.AllowedRowSieve

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawDenominatorFamily31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

structure DenominatorFamily (R : PrincipalMellin.ActualRecipe S η) where

  omega : Frequency R → Detector.PrimitiveFrequencyCharacter F

  distinct : ∀ u v : Frequency R,
    Detector.samePrimitiveFrequencyCharacter F (omega u) (omega v) → u = v

  conductor_bound : ∃ c : ℝ, 0 < c ∧ ∀ u : Frequency R,
    (Ideal.absNorm (omega u).conductor : ℝ) ≤ c * frequencyNorm R u

  raw_minus : ∀ (u : Frequency R) (U : AllRowEuler.InitialSeparation.RawFrequency R.A),
    U.u = u.val.val → ∀ I : R.A.Exterior,
      AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target U I =
        Detector.deletedPrimitiveIdealCoefficient F (omega u)
          (RawHeckeRows.rawDeletionSet U) I.val

variable (R : PrincipalMellin.ActualRecipe S η)

theorem exists_denominatorFamily : Nonempty (DenominatorFamily R) := by
  obtain ⟨ω, h1, h2, h3, h4⟩ := RawDenominatorExistence.raw_denominator_existence R
  exact ⟨⟨ω, h3, h4, h1⟩⟩

def denominatorFamily : DenominatorFamily R := (exists_denominatorFamily R).some

theorem eq_principalFrequency_iff (u : Frequency R) :
    u = principalFrequency R ↔ u.val.val = 1 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    exact Subtype.ext (Subtype.ext h)

theorem frequency_count_lt :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      {u : Frequency R | frequencyNorm R u < X}.Finite ∧
      ((({u : Frequency R | frequencyNorm R u < X}).ncard : ℕ) : ℝ) ≤ C * X :=
  RawFrequencyCount.frequency_count_lt R

theorem frequency_dyad_count :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
      {u : Frequency R | U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U}.Finite ∧
      ((({u : Frequency R | U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U}).ncard : ℕ) : ℝ)
        ≤ C * U :=
  RawFrequencyCount.frequency_dyad_count R

def dyadNonprincipal (U : ℝ) : Set (Frequency R) :=
  {u | u ≠ principalFrequency R ∧ U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U}

theorem denominator_conductor_le :
    ∃ c : ℝ, 0 < c ∧ ∀ u : Frequency R,
      (Ideal.absNorm ((denominatorFamily R).omega u).conductor : ℝ) ≤ c * frequencyNorm R u :=
  (denominatorFamily R).conductor_bound

theorem denominator_local_tuples :
    ∃ L : Set (Detector.FixedSResidue.FullLocalCharacters R.A), L.Finite ∧
      (∀ σ ∈ L, Detector.FixedSResidue.HasFiniteOrder R.A σ) ∧
      ∀ u : Frequency R, ∃ σ ∈ L,
        Detector.HasFixedFullSLocalTuple F R.A ((denominatorFamily R).omega u) σ := by
  obtain ⟨L, hL, hord, hcov⟩ := RawLocalTupleCover31.raw_local_tuple_cover R
  exact ⟨L, hL, hord, hcov (denominatorFamily R).omega (denominatorFamily R).raw_minus⟩

theorem raw_conductor_sieve :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (U N : ℝ), 2 ≤ U → 2 ≤ N →
        ∀ (J : Finset (Frequency R)),
          (∀ u ∈ J, U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U) →
          ∀ (B : Finset (Ideal (𝓞 F))),
            (∀ I ∈ B, I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ N) →
            ∀ b : Ideal (𝓞 F) → ℂ,
              (∑ u ∈ J, ‖∑ I ∈ B, b I * ((denominatorFamily R).omega u).character I‖ ^ 2) ≤
                C * (N + U ^ 2) * (N * U) ^ ε * ∑ I ∈ B, ‖b I‖ ^ 2 := by
  intro ε hε
  obtain ⟨c, hc, hcond⟩ := denominator_conductor_le R
  obtain ⟨L, hL, hord, hcov⟩ := denominator_local_tuples R
  obtain ⟨C, hC, h⟩ :=
    AllIdealSieveTransfer31.all_ideal_sieve_transfer_frequency R c hc L hL hord ε hε
  refine ⟨C, hC, fun U N hU hN J hJ B hB b => ?_⟩
  exact h U N hU hN (denominatorFamily R).omega (denominatorFamily R).distinct hcond hcov J
    (fun u hu => (hJ u hu).2) B hB b

theorem raw_conductor_sieve_finsum :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (U N : ℝ), 2 ≤ U → 2 ≤ N →
        ∀ (J : Finset (Frequency R)),
          (∀ u ∈ J, U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U) →
          ∀ b : Ideal (𝓞 F) → ℂ,
            (∀ I, b I ≠ 0 → I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ N) →
              (∑ u ∈ J,
                ‖∑ᶠ I : Ideal (𝓞 F), b I * ((denominatorFamily R).omega u).character I‖ ^ 2) ≤
                C * (N + U ^ 2) * (N * U) ^ ε * ∑ᶠ I : Ideal (𝓞 F), ‖b I‖ ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := raw_conductor_sieve R ε hε
  refine ⟨C, hC, fun U N hU hN J hJ b hb => ?_⟩
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ ⌊N⌋₊}.Finite :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊N⌋₊).subset (fun I hI => hI.2)
  obtain ⟨B, hmem⟩ : ∃ B : Finset (Ideal (𝓞 F)),
      ∀ I, I ∈ B ↔ I ≠ ⊥ ∧ Ideal.absNorm I ≤ ⌊N⌋₊ :=
    ⟨hfin.toFinset, fun I => hfin.mem_toFinset⟩
  have hB : ∀ I ∈ B, I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ N := by
    intro I hI
    obtain ⟨h1, h2⟩ := (hmem I).1 hI
    refine ⟨h1, le_trans ?_ (Nat.floor_le (by linarith : (0 : ℝ) ≤ N))⟩
    exact Nat.cast_le.mpr h2
  have hsupp : ∀ I, b I ≠ 0 → I ∈ B := by
    intro I hI
    obtain ⟨h1, h2⟩ := hb I hI
    exact (hmem I).2 ⟨h1, Nat.le_floor h2⟩
  have hs1 : ∀ u : Frequency R,
      ∑ᶠ I : Ideal (𝓞 F), b I * ((denominatorFamily R).omega u).character I =
        ∑ I ∈ B, b I * ((denominatorFamily R).omega u).character I := by
    intro u
    apply finsum_eq_sum_of_support_subset
    intro I hI
    have h1 : b I * ((denominatorFamily R).omega u).character I ≠ 0 := hI
    exact Finset.mem_coe.mpr (hsupp I (left_ne_zero_of_mul h1))
  have hs2 : ∑ᶠ I : Ideal (𝓞 F), ‖b I‖ ^ 2 = ∑ I ∈ B, ‖b I‖ ^ 2 := by
    apply finsum_eq_sum_of_support_subset
    intro I hI
    have h1 : ‖b I‖ ^ 2 ≠ 0 := hI
    have h2 : b I ≠ 0 := fun h0 => h1 (by simp [h0])
    exact Finset.mem_coe.mpr (hsupp I h2)
  have hA : ∑ u ∈ J, ‖∑ᶠ I : Ideal (𝓞 F), b I * ((denominatorFamily R).omega u).character I‖ ^ 2
      = ∑ u ∈ J, ‖∑ I ∈ B, b I * ((denominatorFamily R).omega u).character I‖ ^ 2 :=
    Finset.sum_congr rfl (fun u _ => by rw [hs1 u])
  rw [hA, hs2]
  exact h U N hU hN J hJ B hB b

end

end DedekindZetaZeroFree.Quantitative.RawDenominatorFamily31
