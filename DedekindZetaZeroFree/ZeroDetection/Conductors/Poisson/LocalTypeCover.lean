module

public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.DenominatorExistence

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawLocalTupleCover31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
open scoped Classical

section Copied

open DedekindZetaZeroFree.Detector IsDedekindDomain

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

private theorem frequency_denominator_full_local_tuples
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)]
    (η : PrimitiveFrequencyCharacter F) (hηS : conductorSupportedOn F S η)
    (A : SArithmeticData F) (hAS : (A.Sf : Set (HeightOneSpectrum (𝓞 F))) = S) :
    ∃ L : Set (Detector.FixedSResidue.FullLocalCharacters A), L.Finite ∧
      (∀ σ ∈ L, Detector.FixedSResidue.HasFiniteOrder A σ) ∧
      ∀ (U : FrequencyRepresentatives F S)
        (K : KummerFrequencyFamily F ζ12 ι S U)
        (T : TwistedFrequencyFamily F ζ12 ι S U K η) (u : U.carrier),
        ∃ σ ∈ L, HasFixedFullSLocalTuple F A (T.denominator u) σ := by
  classical
  obtain ⟨P, Q, hfin, hlocal⟩ :=
    frequency_rows_finite_ramified_local_types F ζ12 hζ12 ι S hS hSix η hηS
  let index : {v // v ∈ A.Sf} → S := fun v => ⟨v.val, hAS ▸ v.property⟩
  let R := Set.univ.pi (fun v : {v // v ∈ A.Sf} => Q (index v))
  have hR : R.Finite := Set.Finite.pi (fun v => (hfin (index v)).2)
  let tuple : ((v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ →ₜ* ℂˣ) →
      Detector.FixedSResidue.FullLocalCharacters A :=
    fun δ => (fun _ => 1, fun v => (δ v).toMonoidHom)
  let L := (tuple '' R) ∩ {σ | Detector.FixedSResidue.HasFiniteOrder A σ}
  refine ⟨L, (hR.image tuple).inter_of_left _, fun σ hσ => hσ.2, ?_⟩
  intro U K T u
  choose δ hδmem hδlocal using fun v : {v // v ∈ A.Sf} =>
    (hlocal U K T u (index v)).2
  have hδR : δ ∈ R := by
    intro v hv
    exact hδmem v
  have hfiniteOrder : Detector.FixedSResidue.HasFiniteOrder A (tuple δ) := by
    let χ := T.denominator u
    let hc := primitive12_totallyComplex F ζ12 hζ12
    let k := Nat.card (ClassFieldTheory.RayClassGroup
      (RayClassBridge.narrowIdealModulus F χ.conductor χ.conductor_ne_zero))
    refine ⟨k, RayClassBridge.ideleClassCharacter_exponent_pos F χ.conductor
      χ.conductor_ne_zero, ?_, ?_⟩
    · intro w x
      simp [tuple]
    · intro v x
      have hcan : Conductor.Raw.IsFrequencyLocalComponent F χ v.val
          (Conductor.canonicalFrequencyLocalCharacter F hc χ v.val) :=
        Conductor.LocalTwistSteps.idelic_restriction_is_raw_local_component
          F hc χ v.val _ (by intro x; rfl)
      have heq := Conductor.LocalTwistSteps.raw_local_component_unique
        F χ v.val (δ v) _ (hδlocal v) hcan
      change δ v x ^ k = 1
      rw [heq]
      exact Conductor.canonicalFrequencyLocalCharacter_pow_card F hc χ v.val x
  refine ⟨tuple δ, ⟨⟨δ, hδR, rfl⟩, hfiniteOrder⟩, ?_, ?_⟩
  · intro w
    rfl
  · intro v
    exact ⟨δ v, rfl, hδlocal v⟩

end Copied

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem raw_local_tuple_cover (R : PrincipalMellin.ActualRecipe S η) :
    ∃ L : Set (Detector.FixedSResidue.FullLocalCharacters R.A), L.Finite ∧
      (∀ σ ∈ L, Detector.FixedSResidue.HasFiniteOrder R.A σ) ∧
      ∀ ω : Frequency R → Detector.PrimitiveFrequencyCharacter F,
        (∀ (u : Frequency R) (U : AllRowEuler.InitialSeparation.RawFrequency R.A),
          U.u = u.val.val → ∀ I : R.A.Exterior,
            AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target U I =
              Detector.deletedPrimitiveIdealCoefficient F (ω u)
                (RawHeckeRows.rawDeletionSet U) I.val) →
        ∀ u : Frequency R, ∃ σ ∈ L,
          Detector.HasFixedFullSLocalTuple F R.A (ω u) σ := by
  classical
  letI : IsPrincipalIdealRing R.A.R :=
    R.A.principalIdealRing_of_classGroup_subsingleton R.classKilled
  have hSix : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 →
        v ∈ (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) := by
    intro v hv
    by_contra hout
    exact hv (ArithmeticContext.actual_outside_norm_coprime_six R.A v hout)
  obtain ⟨V, e, he, hnorm⟩ :=
    MinusArithmetic.actual_detector_frequency_representatives R
  obtain ⟨K⟩ := Detector.kummer_frequency_family_exists F R.A.zeta12
    R.A.primitive_zeta12 R.σ (R.A.Sf : Set _) R.A.Sf.finite_toSet hSix V
  obtain ⟨η0, hη0, _, htarget⟩ := MinusArithmetic.target_primitive_inducer R
  obtain ⟨T, hT⟩ :=
    MinusArithmetic.raw_minus_family_identification R V e he K η0 hη0 htarget
  obtain ⟨L, hL, hOrder, hType⟩ :=
    frequency_denominator_full_local_tuples F R.A.zeta12 R.A.primitive_zeta12
      R.σ (R.A.Sf : Set _) R.A.Sf.finite_toSet hSix η0 hη0 R.A rfl
  obtain ⟨_, Ufam, _, hUfam⟩ := RawHeckeRows.actual_context_and_raw_frequencies R
  refine ⟨L, hL, hOrder, ?_⟩
  intro ω hω u
  have hEq : ω u = T.denominator (e u) :=
    MinusArithmetic.deleted_primitive_inducers_eq R.A
      (RawHeckeRows.rawDeletionSet (Ufam u))
      (RawDenominatorExistence.rawDeletionSet_finite R (Ufam u))
      (RawDenominatorExistence.Sf_subset_rawDeletionSet R (Ufam u))
      (ω u) (T.denominator (e u))
      (fun I => (hω u (Ufam u) (hUfam u) I).symm.trans (hT u (Ufam u) (hUfam u) I))
  rw [hEq]
  exact hType V K T (e u)

end

end DedekindZetaZeroFree.Quantitative.RawLocalTupleCover31
