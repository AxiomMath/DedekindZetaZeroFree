module

public import DedekindZetaZeroFree.Arithmetic.Kummer.SexticCharacterOrder
public import DedekindZetaZeroFree.ZeroDetection.Conductors.SexticLocalExponentBounds
public import DedekindZetaZeroFree.ZeroDetection.Conductors.ExteriorRamificationNormBound
public import DedekindZetaZeroFree.Arithmetic.Ideals.ExteriorPrimeRadicalNormBound
public import DedekindZetaZeroFree.LFunctions.Hecke.PrimitiveTwists.LocalComponents
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterUnitarity

@[expose] public section

section

open scoped NumberField
open IsDedekindDomain
namespace DedekindZetaZeroFree.Detector.Conductor

theorem numerator_exterior_ramified_valuation_lt_one
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F)))
    (U : FrequencyRepresentatives F S) (K : KummerFrequencyFamily F ζ12 ι S U)
    (u : U.carrier) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S)
    (hRam : (K.numerator u).conductor ≤ v.asIdeal) :
    v.valuation F (u.val : F) < 1 := by
  have hle : v.valuation F (u.val : F) ≤ 1 := (U.power_free u.val u.property).1 v hv
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hcop := (K.kummer u v hv heq).1
  have htop : (⊤ : Ideal (𝓞 F)) ≤ v.asIdeal := by
    rw [← hcop]
    exact sup_le le_rfl hRam
  exact v.isPrime.ne_top (top_unique htop)

theorem numerator_radical_estimate
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F), ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : FrequencyRepresentatives F S) (K : KummerFrequencyFamily F ζ12 ι S U)
        (u : U.carrier),
        (Ideal.absNorm (K.numerator u).conductor : ℝ) ≤
          C * (Raw.frequencyRadicalSNorm F S U u : ℝ) := by
  classical
  obtain ⟨b, hbTame, hb⟩ := LocalExponent.sextic_conductor_exponent_bounds F
  obtain ⟨C, hC, hNorm⟩ :=
    NormFactorization.norm_le_exterior_prime_product F S hS b
  refine ⟨C, hC, ?_⟩
  intro U K u
  let I := (K.numerator u).conductor
  have hI : I ≠ ⊥ := (K.numerator u).conductor_ne_zero
  have hFinite : {v : HeightOneSpectrum (𝓞 F) | I ≤ v.asIdeal}.Finite := by
    simpa only [Ideal.dvd_iff_le] using (Ideal.finite_factors hI)
  let T := hFinite.toFinset.filter (fun v => v ∉ S)
  have hT : ∀ v, v ∈ T ↔ I ≤ v.asIdeal ∧ v ∉ S := by
    intro v
    simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hExp : ∀ v : HeightOneSpectrum (𝓞 F),
      (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal ≤ b v :=
    hb (K.numerator u)
      (global_kummer_sixth_power F ζ12 hζ12 ι S hS u.val (K.numerator u) (K.kummer u))
  have hNormI : (Ideal.absNorm I : ℝ) ≤
      C * (∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ)) := by
    apply hNorm I hI T
    · intro v _
      exact hExp v
    · intro v hv
      have hCop : (Ideal.absNorm v.asIdeal).Coprime 6 := by
        by_contra hn
        exact hv (hSix v hn)
      simpa only [hbTame v hCop] using hExp v
    · intro v hv hRam
      exact (hT v).mpr ⟨hRam, hv⟩
  have ha : Raw.frequencySInteger F S U u ≠ 0 := by
    intro hz
    have hzF := congrArg (fun a : S.integer F => (a : F)) hz
    exact u.val.ne_zero hzF
  have hRad : (∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ)) ≤
      (Raw.frequencyRadicalSNorm F S U u : ℝ) := by
    apply RadicalQuotient.exterior_prime_product_le_radical_index F S hS
      (Raw.frequencySInteger F S U u) ha T
    intro v hv
    obtain ⟨hRam, hvS⟩ := (hT v).mp hv
    exact ⟨hvS,
      numerator_exterior_ramified_valuation_lt_one F ζ12 ι S U K u v hvS hRam⟩
  exact hNormI.trans (mul_le_mul_of_nonneg_left hRad (le_of_lt hC))

end DedekindZetaZeroFree.Detector.Conductor

end

section

open scoped NumberField
open IsDedekindDomain

namespace DedekindZetaZeroFree.Detector.Conductor.LocalTwistSteps

theorem primitive_twist_idelic_restriction
    (F : Type) [Field F] [NumberField F] (hc : NumberField.IsTotallyComplex F)
    (η χ ψ : PrimitiveFrequencyCharacter F)
    (htw : IsPrimitiveFrequencyTwist F η χ ψ)
    (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    RayClassBridge.ideleClassCharacter F hc
        ψ.conductor ψ.conductor_ne_zero ψ.character
        (IdeleGroup.finitePlaceIdeleClass v u) =
      RayClassBridge.ideleClassCharacter F hc
        η.conductor η.conductor_ne_zero η.character
        (IdeleGroup.finitePlaceIdeleClass v u) /
      RayClassBridge.ideleClassCharacter F hc
        χ.conductor χ.conductor_ne_zero χ.character
        (IdeleGroup.finitePlaceIdeleClass v u) := by
  exact Conductor.canonical_idelic_primitive_twist F hc η χ ψ htw
    (IdeleGroup.finitePlaceIdeleClass v u)

end DedekindZetaZeroFree.Detector.Conductor.LocalTwistSteps

end

section

open scoped NumberField
open IsDedekindDomain
namespace DedekindZetaZeroFree.Detector.Conductor

noncomputable def canonicalFrequencyLocalHom
    (F : Type) [Field F] [NumberField F] (hc : NumberField.IsTotallyComplex F)
    (χ : PrimitiveFrequencyCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* ℂˣ :=
  (RayClassBridge.ideleClassCharacter F hc χ.conductor χ.conductor_ne_zero χ.character).comp
    (IdeleGroup.finitePlaceIdeleClass v)

theorem canonicalFrequencyLocalHom_continuous
    (F : Type) [Field F] [NumberField F] (hc : NumberField.IsTotallyComplex F)
    (χ : PrimitiveFrequencyCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (canonicalFrequencyLocalHom F hc χ v) := by
  apply continuous_of_continuousAt_one
  apply Filter.EventuallyEq.continuousAt (y := (1 : ℂˣ))
  let n := (RayClassBridge.narrowIdealModulus F χ.conductor χ.conductor_ne_zero).finitePart v
  have hnhds := (ClassFieldTheory.isOpen_rayLocalHigherUnitGroup v n).mem_nhds
    (ClassFieldTheory.rayLocalHigherUnitGroup v n).one_mem
  filter_upwards [hnhds] with u hu
  exact RayClassBridge.ideleClassCharacter_finitePlaceIdeleClass_higherUnit F hc
    χ.conductor χ.conductor_ne_zero χ.character v u hu

noncomputable def canonicalFrequencyLocalCharacter
    (F : Type) [Field F] [NumberField F] (hc : NumberField.IsTotallyComplex F)
    (χ : PrimitiveFrequencyCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →ₜ* ℂˣ where
  __ := canonicalFrequencyLocalHom F hc χ v
  continuous_toFun := canonicalFrequencyLocalHom_continuous F hc χ v

theorem canonicalFrequencyLocalCharacter_pow_card
    (F : Type) [Field F] [NumberField F] (hc : NumberField.IsTotallyComplex F)
    (χ : PrimitiveFrequencyCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    canonicalFrequencyLocalCharacter F hc χ v u ^
      Nat.card (ClassFieldTheory.RayClassGroup
        (RayClassBridge.narrowIdealModulus F χ.conductor χ.conductor_ne_zero)) = 1 := by
  exact RayClassBridge.ideleClassCharacter_pow_card F hc χ.conductor
    χ.conductor_ne_zero χ.character (IdeleGroup.finitePlaceIdeleClass v u)

theorem primitive_twist_local_range_finite_of_local_compatibility
    (F : Type) [Field F] [NumberField F]
    (η : PrimitiveFrequencyCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (ε : (v.adicCompletion F)ˣ →ₜ* ℂˣ)
    (hcompat : ∀ (χ ψ : PrimitiveFrequencyCharacter F),
      IsPrimitiveFrequencyTwist F η χ ψ →
      ∀ δ : (v.adicCompletion F)ˣ →ₜ* ℂˣ,
        Raw.IsFrequencyLocalComponent F χ v δ →
        Raw.IsFrequencyLocalComponent F ψ v (ε / δ))
    (A : Set ((v.adicCompletion F)ˣ →ₜ* ℂˣ)) (hA : A.Finite) :
    ∃ B : Set ((v.adicCompletion F)ˣ →ₜ* ℂˣ), B.Finite ∧
      ∀ (χ ψ : PrimitiveFrequencyCharacter F),
        IsPrimitiveFrequencyTwist F η χ ψ →
        (∃ δ ∈ A, Raw.IsFrequencyLocalComponent F χ v δ) →
        ∃ δ ∈ B, Raw.IsFrequencyLocalComponent F ψ v δ := by
  refine ⟨(fun δ => ε / δ) '' A, hA.image _, ?_⟩
  intro χ ψ htw hχ
  obtain ⟨δ, hδA, hδχ⟩ := hχ
  exact ⟨ε / δ, ⟨δ, hδA, rfl⟩, hcompat χ ψ htw δ hδχ⟩

theorem primitive_twist_local_range_finite
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12)
    (η : PrimitiveFrequencyCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (A : Set ((v.adicCompletion F)ˣ →ₜ* ℂˣ)) (hA : A.Finite) :
    ∃ B : Set ((v.adicCompletion F)ˣ →ₜ* ℂˣ), B.Finite ∧
      ∀ (χ ψ : PrimitiveFrequencyCharacter F),
        IsPrimitiveFrequencyTwist F η χ ψ →
        (∃ δ ∈ A, Raw.IsFrequencyLocalComponent F χ v δ) →
        ∃ δ ∈ B, Raw.IsFrequencyLocalComponent F ψ v δ := by
  let hc : NumberField.IsTotallyComplex F := primitive12_totallyComplex F ζ12 hζ12
  let ε := canonicalFrequencyLocalCharacter F hc η v
  apply primitive_twist_local_range_finite_of_local_compatibility F η v ε ?_ A hA
  intro χ ψ htw δ hδ
  have hχ : Raw.IsFrequencyLocalComponent F χ v
      (canonicalFrequencyLocalCharacter F hc χ v) :=
    LocalTwistSteps.idelic_restriction_is_raw_local_component F hc χ v _
      (by intro u; rfl)
  have hψ : Raw.IsFrequencyLocalComponent F ψ v
      (canonicalFrequencyLocalCharacter F hc ψ v) :=
    LocalTwistSteps.idelic_restriction_is_raw_local_component F hc ψ v _
      (by intro u; rfl)
  have hδ : δ = canonicalFrequencyLocalCharacter F hc χ v :=
    LocalTwistSteps.raw_local_component_unique F χ v δ _ hδ hχ
  have htw' : canonicalFrequencyLocalCharacter F hc ψ v =
      ε / canonicalFrequencyLocalCharacter F hc χ v := by
    ext u
    exact congrArg (fun z : ℂˣ => (z : ℂ))
      (LocalTwistSteps.primitive_twist_idelic_restriction F hc η χ ψ htw v u)
  rw [hδ, ← htw']
  exact hψ

end DedekindZetaZeroFree.Detector.Conductor

end

section

open scoped NumberField
open IsDedekindDomain
namespace DedekindZetaZeroFree.Detector.Conductor

theorem finite_order_characters_of_finite_power_quotient
    (G : Type*) [CommGroup G] [TopologicalSpace G]
    (n : ℕ) [NeZero n] [Finite (G ⧸ (powMonoidHom (α := G) n).range)] :
    {δ : G →ₜ* ℂˣ | ∀ x, δ x ^ n = 1}.Finite := by
  classical
  let Q := G ⧸ (powMonoidHom (α := G) n).range
  let lift (δ : {δ : G →ₜ* ℂˣ | ∀ x, δ x ^ n = 1}) : Q →* ℂˣ :=
    QuotientGroup.lift _ δ.val.toMonoidHom (by
      rintro x ⟨y, rfl⟩
      change δ.val (y ^ n) = 1
      rw [map_pow, δ.property])
  let encode (δ : {δ : G →ₜ* ℂˣ | ∀ x, δ x ^ n = 1}) : Q → rootsOfUnity n ℂ :=
    fun q => ⟨lift δ q, by
      induction q using QuotientGroup.induction_on with
      | H x =>
        change δ.val x ∈ rootsOfUnity n ℂ
        exact (mem_rootsOfUnity _ _).mpr (δ.property x)⟩
  apply Set.finite_coe_iff.mp
  apply Finite.of_injective encode
  intro δ ε h
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro x
  have hx := congrFun h (QuotientGroup.mk x : Q)
  exact congrArg Subtype.val hx

theorem finite_sextic_continuous_local_characters
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    {δ : (v.adicCompletion F)ˣ →ₜ* ℂˣ | ∀ x, δ x ^ (6 : ℕ) = 1}.Finite := by
  letI : ValuativeRel (v.adicCompletion F) :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel F v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v
  letI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_ringHom (NumberField.FinitePlace.embedding (K := F) v).injective
  letI : Finite ((v.adicCompletion F)ˣ ⧸
      (powMonoidHom (α := (v.adicCompletion F)ˣ) 6).range) := by
    change Finite (ClassFieldTheory.PowerClassGroup (v.adicCompletion F) ⟨6, by decide⟩)
    exact ClassFieldTheory.powerClassGroup_finite _ _ (by norm_num)
  exact finite_order_characters_of_finite_power_quotient _ 6

theorem sextic_local_components_finite_of_exists
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (hExists : ∀ χ : PrimitiveFrequencyCharacter F,
      (∀ n : Ideal (𝓞 F), n ≠ ⊥ → n ⊔ χ.conductor = ⊤ →
        χ.character n ^ (6 : ℕ) = 1) →
      ∃ δ : (v.adicCompletion F)ˣ →ₜ* ℂˣ,
        (∀ x, δ x ^ (6 : ℕ) = 1) ∧ Raw.IsFrequencyLocalComponent F χ v δ) :
    ∃ A : Set ((v.adicCompletion F)ˣ →ₜ* ℂˣ), A.Finite ∧
      ∀ χ : PrimitiveFrequencyCharacter F,
        (∀ n : Ideal (𝓞 F), n ≠ ⊥ → n ⊔ χ.conductor = ⊤ →
          χ.character n ^ (6 : ℕ) = 1) →
        ∃ δ ∈ A, Raw.IsFrequencyLocalComponent F χ v δ := by
  refine ⟨{δ | ∀ x, δ x ^ (6 : ℕ) = 1},
    finite_sextic_continuous_local_characters F v, ?_⟩
  intro χ hχ
  obtain ⟨δ, hδ, hlocal⟩ := hExists χ hχ
  exact ⟨δ, hδ, hlocal⟩

 def rayPower
    (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (η : RayClassCharacter F m) (n : ℕ) (hn : 0 < n) :
    RayClassCharacter F m where
  toFun I := η I ^ n
  map_mul' I J := by rw [η.map_mul', mul_pow]
  map_top' := by rw [η.map_top', one_pow]
  eq_zero_iff' I := by rw [pow_eq_zero_iff (Nat.ne_of_gt hn), η.eq_zero_iff']
  map_span' a ha hm hpos := by rw [η.map_span' a ha hm hpos, one_pow]

theorem fractional_character_power
    (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (η : RayClassCharacter F m)
    (n : ℕ) (hn : 0 < n)
    (hη : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ m = ⊤ → η I ^ n = 1) :
    ∀ c, RayClassBridge.fractionalCharacter F m hm η c ^ n = 1 := by
  classical
  let ηn := rayPower F m η n hn
  have hpow : (RayClassBridge.fractionalCharacter F m hm η) ^ n =
      RayClassBridge.fractionalCharacter F m hm ηn := by
    apply RayClassBridge.fractionalCharacter_unique
    intro I hI hcop
    change ((RayClassBridge.fractionalCharacter F m hm η
      (RayClassBridge.integralPrimeTo F m hm I hI hcop)) ^ n : ℂˣ).val = η I ^ n
    rw [Units.val_pow_eq_pow_val, RayClassBridge.fractionalCharacter_integral]
  have hone : (1 : ClassFieldTheory.rayClassPrimeToIdeals
        (RayClassBridge.narrowIdealModulus F m hm) →* ℂˣ) =
      RayClassBridge.fractionalCharacter F m hm ηn := by
    apply RayClassBridge.fractionalCharacter_unique
    intro I hI hcop
    change (1 : ℂ) = η I ^ n
    exact (hη I hI hcop).symm
  intro c
  have hc := DFunLike.congr_fun (hpow.trans hone.symm) c
  exact hc

theorem idelic_character_power
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (η : RayClassCharacter F m)
    (n : ℕ) (hn : 0 < n)
    (hη : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ m = ⊤ → η I ^ n = 1) :
    ∀ c, RayClassBridge.ideleClassCharacter F hcomplex m hm η c ^ n = 1 := by
  have hray : ∀ q, RayClassBridge.rayCharacter F hcomplex m hm η q ^ n = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      exact fractional_character_power F m hm η n hn hη x
  intro c
  exact hray _

theorem canonicalFrequencyLocalCharacter_power
    (F : Type) [Field F] [NumberField F] (hc : NumberField.IsTotallyComplex F)
    (χ : PrimitiveFrequencyCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (n : ℕ) (hn : 0 < n)
    (hχ : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ χ.conductor = ⊤ →
      χ.character I ^ n = 1) :
    ∀ x, canonicalFrequencyLocalCharacter F hc χ v x ^ n = 1 := by
  intro x
  exact idelic_character_power F hc χ.conductor χ.conductor_ne_zero
    χ.character n hn hχ (IdeleGroup.finitePlaceIdeleClass v x)

theorem sextic_local_components_finite
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ A : Set ((v.adicCompletion F)ˣ →ₜ* ℂˣ), A.Finite ∧
      ∀ χ : PrimitiveFrequencyCharacter F,
        (∀ n : Ideal (𝓞 F), n ≠ ⊥ → n ⊔ χ.conductor = ⊤ →
          χ.character n ^ (6 : ℕ) = 1) →
        ∃ δ ∈ A, Raw.IsFrequencyLocalComponent F χ v δ := by
  let hc := primitive12_totallyComplex F ζ12 hζ12
  apply sextic_local_components_finite_of_exists F v
  intro χ hχ
  refine ⟨canonicalFrequencyLocalCharacter F hc χ v,
    canonicalFrequencyLocalCharacter_power F hc χ v 6 (by norm_num) hχ, ?_⟩
  exact LocalTwistSteps.idelic_restriction_is_raw_local_component F hc χ v
    (canonicalFrequencyLocalCharacter F hc χ v) (fun _ => rfl)

end DedekindZetaZeroFree.Detector.Conductor

end

section

open scoped NumberField
open IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.Detector

noncomputable section

def frequencySInteger (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (U : FrequencyRepresentatives F S)
    (u : U.carrier) : S.integer F :=
  ⟨(u.val : F), (U.power_free u.val u.property).1⟩

def frequencySNorm (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (U : FrequencyRepresentatives F S)
    (u : U.carrier) : ℕ :=
  Nat.card ((S.integer F) ⧸ Ideal.span {frequencySInteger F S U u})

def frequencyRadicalSNorm (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (U : FrequencyRepresentatives F S)
    (u : U.carrier) : ℕ :=
  Nat.card ((S.integer F) ⧸ (Ideal.span {frequencySInteger F S U u}).radical)

def idealAwayPrimePart (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  ((normalizedFactors I).filter (fun p => p ≠ v.asIdeal)).prod

def integralElementLocalUnit (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) (ha : a ≠ 0) : (v.adicCompletion F)ˣ :=
  Units.mk0 (NumberField.FinitePlace.embedding v (a : F))
    ((NumberField.FinitePlace.embedding v).injective.ne
      (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ha))

def IsFrequencyLocalComponent (F : Type) [Field F] [NumberField F]
    (χ : PrimitiveFrequencyCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (δ : (v.adicCompletion F)ˣ →ₜ* ℂˣ) : Prop :=
  ∀ (a : 𝓞 F) (ha : a ≠ 0), a - 1 ∈ idealAwayPrimePart F v χ.conductor →
    (δ (integralElementLocalUnit F v a ha) : ℂ) =
      (χ.character (idealAwayPrimePart F v (Ideal.span {a})))⁻¹

def conductorSupportedOn (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (η : PrimitiveFrequencyCharacter F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), η.conductor ≤ v.asIdeal → v ∈ S

theorem frequency_S_norms_finite
    (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (U : FrequencyRepresentatives F S) (u : U.carrier) :
    Finite ((S.integer F) ⧸ Ideal.span {frequencySInteger F S U u}) ∧
      Finite ((S.integer F) ⧸ (Ideal.span {frequencySInteger F S U u}).radical) ∧
      0 < frequencyRadicalSNorm F S U u ∧
      frequencyRadicalSNorm F S U u ≤ frequencySNorm F S U u := by
  classical
  obtain ⟨Sf, rfl⟩ := hS.exists_finset_coe
  have hu : frequencySInteger F (Sf : Set (HeightOneSpectrum (𝓞 F))) U u ≠ 0 := by
    intro h
    have h' := congrArg (fun a : (Sf : Set (HeightOneSpectrum (𝓞 F))).integer F => (a : F)) h
    exact u.val.ne_zero h'
  have hfinite :=
    (sProductModulus_eq_principalIdeal_index F Sf
      (frequencySInteger F (Sf : Set (HeightOneSpectrum (𝓞 F))) U u) hu).1
  letI := hfinite
  have hsurj := Ideal.Quotient.factor_surjective
    (Ideal.le_radical (I := Ideal.span {frequencySInteger F (Sf : Set (HeightOneSpectrum (𝓞 F))) U u}))
  have hrad : Finite (((Sf : Set (HeightOneSpectrum (𝓞 F))).integer F) ⧸
      (Ideal.span {frequencySInteger F (Sf : Set (HeightOneSpectrum (𝓞 F))) U u}).radical) :=
    Finite.of_surjective _ hsurj
  letI := hrad
  exact ⟨hfinite, hrad, Nat.card_pos,
    Nat.card_le_card_of_surjective _ hsurj⟩

theorem frequency_numerator_conductor_bound
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F), ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : FrequencyRepresentatives F S) (K : KummerFrequencyFamily F ζ12 ι S U)
        (u : U.carrier),
        (Ideal.absNorm (K.numerator u).conductor : ℝ) ≤
          C * (frequencyRadicalSNorm F S U u : ℝ) ∧
        C * (frequencyRadicalSNorm F S U u : ℝ) ≤
          C * (frequencySNorm F S U u : ℝ) := by

  suffices hconductor : ∃ C : ℝ, 0 < C ∧
      ∀ (U : FrequencyRepresentatives F S) (K : KummerFrequencyFamily F ζ12 ι S U)
        (u : U.carrier),
        (Ideal.absNorm (K.numerator u).conductor : ℝ) ≤
          C * (frequencyRadicalSNorm F S U u : ℝ) by
    obtain ⟨C, hC, hbound⟩ := hconductor
    refine ⟨C, hC, ?_⟩
    intro U K u
    refine ⟨hbound U K u, ?_⟩
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast (frequency_S_norms_finite F S hS U u).2.2.2) hC.le
  exact Conductor.numerator_radical_estimate F ζ12 hζ12 ι S hS hSix

private theorem no_real_of_mu12 (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : IsEmpty (F →+* ℝ) := by
  constructor
  intro φ
  have h : IsPrimitiveRoot (φ ζ) 12 := hζ.map_of_injective φ.injective
  have he : (φ ζ) ^ 12 = 1 := h.pow_eq_one
  have hs : (φ ζ) ^ 2 = 1 := by
    have he' : ((φ ζ)^2)^6 = 1^6 := by simpa [← pow_mul] using he
    exact (pow_left_inj₀ (sq_nonneg _) (by norm_num) (by norm_num : (6:ℕ) ≠ 0)).mp he'
  have hd := h.dvd_of_pow_eq_one 2 hs
  norm_num at hd

private theorem coprime_of_sub_one_mem {R : Type*} [CommRing R]
    (m : Ideal R) (a : R) (h : a - 1 ∈ m) : Ideal.span {a} ⊔ m = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have ha : a ∈ Ideal.span {a} ⊔ m := Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)
  have hb : a - 1 ∈ Ideal.span {a} ⊔ m := Ideal.mem_sup_right h
  simpa using (Ideal.span {a} ⊔ m).sub_mem ha hb

private theorem nonzero_of_sub_one_mem {R : Type*} [CommRing R]
    (m : Ideal R) (hm : m ≠ ⊤) (a : R) (h : a - 1 ∈ m) : a ≠ 0 := by
  intro ha
  subst a
  apply hm
  apply (Ideal.eq_top_iff_one _).mpr
  simpa using m.neg_mem h

private theorem ray_congruent
    (F : Type) [Field F] [NumberField F] [IsEmpty (F →+* ℝ)]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊤) (χ : RayClassCharacter F m)
    (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : Ideal.span {a} ⊔ m = ⊤) (hab : a - b ∈ m) :
    χ (Ideal.span {a}) = χ (Ideal.span {b}) := by
  have hone : (1 : 𝓞 F) ∈ Ideal.span {a} ⊔ m := by rw [hcop]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hone
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hx
  have hac : a * c - 1 ∈ m := by
    have heq : a * c - 1 = -y := by linear_combination hxy
    rw [heq]
    exact m.neg_mem hy
  have hbc : b * c - 1 ∈ m := by
    have hh := m.mul_mem_right c hab
    have heq : b * c - 1 = (a * c - 1) - (a - b) * c := by ring
    rw [heq]
    exact m.sub_mem hac hh
  have hac0 := nonzero_of_sub_one_mem m hm (a*c) hac
  have hbc0 := nonzero_of_sub_one_mem m hm (b*c) hbc
  have hc0 : c ≠ 0 := (mul_ne_zero_iff.mp hac0).2
  have hca : χ (Ideal.span {a}) * χ (Ideal.span {c}) = 1 := by
    rw [← χ.map_mul', Ideal.span_singleton_mul_span_singleton]
    exact χ.map_span' (a*c) hac0 hac (fun φ => isEmptyElim φ)
  have hcb : χ (Ideal.span {b}) * χ (Ideal.span {c}) = 1 := by
    rw [← χ.map_mul', Ideal.span_singleton_mul_span_singleton]
    exact χ.map_span' (b*c) hbc0 hbc (fun φ => isEmptyElim φ)
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one hca) (hca.trans hcb.symm)

private theorem primitive_twist_conductor_le
    (F : Type) [Field F] [NumberField F] [IsEmpty (F →+* ℝ)]
    (η χ ψ : PrimitiveFrequencyCharacter F)
    (hTwist : IsPrimitiveFrequencyTwist F η χ ψ) :
    η.conductor * χ.conductor ≤ ψ.conductor := by
  by_cases hf : ψ.conductor = ⊤
  · simp [hf]
  by_contra hle
  have hlt : ψ.conductor < ψ.conductor ⊔ (η.conductor * χ.conductor) :=
    lt_of_le_of_ne le_sup_left (fun heq => hle (le_sup_right.trans_eq heq.symm))
  obtain ⟨a, ha, ham, hpos, hcop, hne⟩ := ψ.primitive _ hlt
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ham
  let b : 𝓞 F := 1 + y
  have hab : a - b ∈ ψ.conductor := by
    have heq : a - b = x := by dsimp [b]; linear_combination -hxy
    rw [heq]; exact hx
  have hbm : b - 1 ∈ η.conductor * χ.conductor := by simpa [b] using hy
  have hbcop : Ideal.span {b} ⊔ ψ.conductor = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have hba : a ∈ Ideal.span {b} ⊔ ψ.conductor := by
      have hb := Ideal.mem_sup_left (T := ψ.conductor) (Ideal.mem_span_singleton_self b)
      have hd := Ideal.mem_sup_right (S := Ideal.span {b}) hab
      simpa using (Ideal.span {b} ⊔ ψ.conductor).add_mem hb hd
    have hle' : Ideal.span {a} ⊔ ψ.conductor ≤ Ideal.span {b} ⊔ ψ.conductor :=
      sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hba) le_sup_right
    rw [hcop] at hle'
    exact hle' (by trivial)
  have hb0 : b ≠ 0 := by
    intro hb0
    simp [hb0] at hbcop
    exact hf hbcop
  have hcopm := coprime_of_sub_one_mem (η.conductor * χ.conductor) b hbm
  have hcopall : Ideal.span {b} ⊔ (η.conductor * χ.conductor * ψ.conductor) = ⊤ := by
    apply IsCoprime.sup_eq
    exact (Ideal.isCoprime_iff_sup_eq.mpr hcopm).mul_right
      (Ideal.isCoprime_iff_sup_eq.mpr hbcop)
  have hη : η.character (Ideal.span {b}) = 1 :=
    η.character.map_span' b hb0 (Ideal.mul_le_left hbm) (fun φ => isEmptyElim φ)
  have hχ : χ.character (Ideal.span {b}) = 1 :=
    χ.character.map_span' b hb0 (Ideal.mul_le_right hbm) (fun φ => isEmptyElim φ)
  have hψ := hTwist (Ideal.span {b}) (by simpa using hb0) hcopall
  have heq := ray_congruent F ψ.conductor hf ψ.character a b ha hb0 hcop hab
  apply hne
  rw [heq, hψ, hη, hχ, map_one, mul_one]

theorem frequency_denominator_conductor_bound
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F), ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)]
    (η : PrimitiveFrequencyCharacter F) (hηS : conductorSupportedOn F S η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : FrequencyRepresentatives F S) (K : KummerFrequencyFamily F ζ12 ι S U)
        (T : TwistedFrequencyFamily F ζ12 ι S U K η) (u : U.carrier),
        (Ideal.absNorm (T.denominator u).conductor : ℝ) ≤
          C * (frequencySNorm F S U u : ℝ) := by
  letI := no_real_of_mu12 F ζ12 hζ12
  obtain ⟨C, hC, hbound⟩ :=
    frequency_numerator_conductor_bound F ζ12 hζ12 ι S hS hSix
  have hη : 0 < (Ideal.absNorm η.conductor : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero ((Ideal.absNorm_eq_zero_iff).not.mpr η.conductor_ne_zero))
  refine ⟨(Ideal.absNorm η.conductor : ℝ) * C, mul_pos hη hC, ?_⟩
  intro U K T u
  have hle := primitive_twist_conductor_le F η (K.numerator u) (T.denominator u) (T.induces u)
  have hn : Ideal.absNorm (T.denominator u).conductor ≤
      Ideal.absNorm (η.conductor * (K.numerator u).conductor) := by
    apply Nat.le_of_dvd
    · apply Nat.pos_of_ne_zero
      apply (Ideal.absNorm_eq_zero_iff).not.mpr
      exact mul_ne_zero η.conductor_ne_zero (K.numerator u).conductor_ne_zero
    · exact Ideal.absNorm_dvd_absNorm_of_le hle
  calc
    (Ideal.absNorm (T.denominator u).conductor : ℝ) ≤
        (Ideal.absNorm η.conductor : ℝ) * (Ideal.absNorm (K.numerator u).conductor : ℝ) := by
      exact_mod_cast (by simpa using hn)
    _ ≤ (Ideal.absNorm η.conductor : ℝ) *
        (C * (frequencySNorm F S U u : ℝ)) :=
      mul_le_mul_of_nonneg_left ((hbound U K u).1.trans (hbound U K u).2) hη.le
    _ = _ := by ring

theorem frequency_rows_finite_ramified_local_types
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F), ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)]
    (η : PrimitiveFrequencyCharacter F) (hηS : conductorSupportedOn F S η) :
    ∃ (A B : (v : S) → Set ((v.val.adicCompletion F)ˣ →ₜ* ℂˣ)),
      (∀ v : S, (A v).Finite ∧ (B v).Finite) ∧
      ∀ (U : FrequencyRepresentatives F S) (K : KummerFrequencyFamily F ζ12 ι S U)
        (T : TwistedFrequencyFamily F ζ12 ι S U K η) (u : U.carrier) (v : S),
        (∃ δ ∈ A v, IsFrequencyLocalComponent F (K.numerator u) v.val δ) ∧
        (∃ δ ∈ B v, IsFrequencyLocalComponent F (T.denominator u) v.val δ) := by
  classical
  have hA := fun v : S => Conductor.sextic_local_components_finite F ζ12 hζ12 v.val
  choose A hAfin hAlocal using hA
  have hB := fun v : S => Conductor.primitive_twist_local_range_finite
    F ζ12 hζ12 η v.val (A v) (hAfin v)
  choose B hBfin hBlocal using hB
  refine ⟨A, B, fun v => ⟨hAfin v, hBfin v⟩, ?_⟩
  intro U K T u v
  have hnum := Conductor.global_kummer_sixth_power
    F ζ12 hζ12 ι S hS u.val (K.numerator u) (K.kummer u)
  have hlocal := hAlocal v (K.numerator u) hnum
  exact ⟨hlocal, hBlocal v (K.numerator u) (T.denominator u) (T.induces u) hlocal⟩

end

end DedekindZetaZeroFree.Detector

end
