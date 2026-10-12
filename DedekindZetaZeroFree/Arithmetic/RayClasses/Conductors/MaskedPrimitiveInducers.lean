module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.InitialFrequencyDecomposition
public import DedekindZetaZeroFree.Moments.Reflected.AllRowEulerFactorization

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RawHeckeRows
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def rawDeletionSet {A : SArithmeticData F}
    (U : AllRowEuler.InitialSeparation.RawFrequency A) :
    Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
  (A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ∪
    {v | U.ideal.val ≤ v.asIdeal}

section Raw

variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η' : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem rawDeletionSet_finite
    (U : AllRowEuler.InitialSeparation.RawFrequency A) :
    (rawDeletionSet U).Finite := by
  unfold rawDeletionSet
  apply Set.Finite.union
  · exact A.Sf.finite_toSet
  · let s : Finset (Ideal (𝓞 F)) := (UniqueFactorizationMonoid.normalizedFactors U.ideal.val).toFinset
    have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) :=
      HeightOneSpectrum.asIdeal_injective
    have hsub : {v : HeightOneSpectrum (𝓞 F) | U.ideal.val ≤ v.asIdeal} ⊆
        (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) ⁻¹' (↑s : Set (Ideal (𝓞 F))) := by
      intro v hv
      simp only [Set.mem_preimage, Finset.mem_coe]
      exact Multiset.mem_toFinset.mpr
        ((Ideal.mem_normalizedFactors_iff U.ideal.property.1).mpr ⟨v.isPrime, hv⟩)
    exact (s.finite_toSet.preimage hinj.injOn).subset hsub

private theorem raw_coefficients_zero_at_frequency_primes
    (C : A.GeneralArithmeticContext σ η' hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (p : ExteriorPrime A) (hp : (U.j p).val ≠ 0) :
    AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U (primeIdeal p) = 0 ∧
      AllRowEuler.InitialSeparation.minusExteriorCoefficient σ η' U (primeIdeal p) = 0 := by
  letI : Nontrivial (A.R ⧸ A.extendIdeal (primeIdeal p)) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (A.residue_extendIdeal_ne_top (primeIdeal p) p.val.isPrime.ne_top)
  have hg : Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (generator C p) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← (generator_generates C p).2]
    exact Ideal.mem_span_singleton_self _
  have hu : Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u = 0 := by
    rw [(AllRowEuler.InitialSeparation.RawFrequency.unitPart_spec C U p).1, map_mul, map_pow,
      hg, zero_pow hp, zero_mul]
  have hchi : chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) = 0 := by
    rw [hu, MulChar.map_zero]
  refine ⟨?_, ?_⟩
  · exact hchi
  · rw [AllRowEuler.InitialSeparation.minusExteriorCoefficient]
    rw [show AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U (primeIdeal p) =
      chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) from rfl,
      hchi, star_zero, mul_zero]

private theorem raw_exterior_prime_identification
    (C : A.GeneralArithmeticContext σ η' hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (χ ψ : Detector.PrimitiveFrequencyCharacter F)
    (hχ : Detector.IsKummerFrequencyCharacter F A.zeta12 σ
      (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
      (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) χ)
    (hψ : Detector.conductorSupportedOn F (rawDeletionSet U) ψ)
    (htwist : ∀ J : Ideal (𝓞 F), J ≠ ⊥ →
      J ⊔ (A.modulus * χ.conductor * ψ.conductor) = ⊤ →
      ψ.character J = η' J * star (χ.character J)) :
    ∀ p : ExteriorPrime A, (U.j p).val = 0 →
      (p.val.asIdeal ⊔ χ.conductor = ⊤ ∧ p.val.asIdeal ⊔ ψ.conductor = ⊤ ∧
        p.val.asIdeal ⊔ A.modulus = ⊤) ∧
      (AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U (primeIdeal p) =
        χ.character p.val.asIdeal ∧
       AllRowEuler.InitialSeparation.minusExteriorCoefficient σ η' U (primeIdeal p) =
        ψ.character p.val.asIdeal) := by
  classical
  intro p hj
  have hv : p.val ∉ A.Sf :=
    ArithmeticContext.actual_exterior_prime_outside A (primeIdeal p) p.val rfl
  have he : idealPrimeExponent p.val.asIdeal U.ideal.val = 0 := hj
  have hnot : ¬ U.ideal.val ≤ p.val.asIdeal := by
    intro hle
    have hm := (Ideal.mem_normalizedFactors_iff U.ideal.property.1).mpr
      ⟨p.val.isPrime, hle⟩
    exact (Multiset.count_eq_zero.mp he) hm
  have huval : p.val.valuation F (U.u : F) = 1 := by
    exact ArithmeticContext.actual_generator_valuation_unit A U.ideal U.u
      (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) U.generates rfl p.val hv hnot
  obtain ⟨hpc, j, hjval, hjchar⟩ := hχ p.val hv huval
  have hpp : p.val.asIdeal ⊔ ψ.conductor = ⊤ := by
    apply (codisjoint_iff.mp ((Ideal.isMaximal_def.mp p.val.isMaximal).not_le_iff_codisjoint.mp ?_))
    intro hle
    rcases hψ p.val hle with h | h
    · exact hv h
    · exact hnot h
  have hpm : p.val.asIdeal ⊔ A.modulus = ⊤ := by
    apply (codisjoint_iff.mp ((Ideal.isMaximal_def.mp p.val.isMaximal).not_le_iff_codisjoint.mp ?_))
    intro hle
    exact hv (A.modulus_support p.val hle)
  have htw := htwist p.val.asIdeal p.val.ne_bot (by
    rw [Ideal.sup_mul_eq_of_coprime_right hpp,
      Ideal.sup_mul_eq_of_coprime_right hpc, hpm])
  have hunit : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) := by
    have hs := AllRowEuler.InitialSeparation.RawFrequency.unitPart_spec C U p
    rw [hj, pow_zero, one_mul] at hs
    rw [hs.1]
    exact hs.2
  let q := Ideal.Quotient.mk (A.extendIdeal (primeIdeal p))
  let z : A.R := algebraMap (𝓞 F) A.R A.primitive_zeta12.toInteger
  have hz : (z : F) = A.zeta12 := A.primitive_zeta12.coe_toInteger
  have hred : q (z ^ (2 * j.val)) = q U.u ^ ((Ideal.absNorm p.val.asIdeal - 1) / 6) := by
    have hlt : p.val.valuation F
        ((U.u ^ ((Ideal.absNorm p.val.asIdeal - 1) / 6) - z ^ (2 * j.val) : A.R) : F) < 1 := by
      simpa only [Units.val_mk0, Subalgebra.coe_sub, Subalgebra.coe_pow, hz, pow_mul] using hjval
    have hzero : q (U.u ^ ((Ideal.absNorm p.val.asIdeal - 1) / 6) - z ^ (2 * j.val)) = 0 := by
      apply (A.exteriorLocalResidueEquiv (primeIdeal p) p.val rfl).injective
      rw [map_zero]
      change (A.exteriorLocalResidueEquiv (primeIdeal p) p.val rfl)
        (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) _) = 0
      rw [A.exteriorLocalResidueEquiv_apply (primeIdeal p) p.val rfl]
      apply (IsLocalRing.residue_eq_zero_iff _).mpr
      apply (Valuation.mem_maximalIdeal_iff (p.val.adicCompletion F) Valued.v).mpr
      change Valued.v ((WithVal.toVal (p.val.valuation F)
        ((U.u ^ ((Ideal.absNorm p.val.asIdeal - 1) / 6) - z ^ (2 * j.val) : A.R) : F) :
        WithVal (p.val.valuation F)) : p.val.adicCompletion F) < 1
      rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    rw [map_sub, map_pow] at hzero
    exact (sub_eq_zero.mp hzero).symm
  obtain ⟨u, hu⟩ := hunit
  obtain ⟨k, hk, hkchar, hkred⟩ :=
    A.sexticResidueFamily_normalized.2.1 (primeIdeal p) p.val rfl u
  rw [A.exteriorResidue_card, hu] at hkred
  have hkj : k = j.val :=
    (A.exterior_sextic_primitive (primeIdeal p) p.val.isPrime.ne_top).pow_inj hk j.isLt (by
      have hh := hkred.trans hred.symm
      simpa only [z, ← map_pow, pow_mul] using hh)
  have hchi : chi (σ := σ) p (q U.u) = χ.character p.val.asIdeal := by
    rw [← hu]
    simp only [chi, SArithmeticData.sexticResiduePowerChar, SArithmeticData.sexticExponent,
      show (1 : ℤ) % 6 = 1 from rfl, Int.toNat_one, pow_one, MulChar.ofUnitHom_coe,
      MonoidHom.comp_apply, Units.coe_map, hkchar, hkj, hjchar, pow_mul]
    rfl
  refine ⟨⟨hpc, hpp, hpm⟩, ?_, ?_⟩
  · exact hchi
  · rw [AllRowEuler.InitialSeparation.minusExteriorCoefficient]
    rw [show AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U (primeIdeal p) =
      chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) from rfl]
    rw [hchi]
    exact htw.symm

private theorem raw_multiplicative_mask_identification
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (χ : Detector.PrimitiveFrequencyCharacter F)
    (f : Ideal (𝓞 F) → ℂ) (hone : f ⊤ = 1)
    (hmul : ∀ I J : Ideal (𝓞 F), f (I * J) = f I * f J)
    (houtside : ∀ I : Ideal (𝓞 F), ¬ (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) → f I = 0)
    (hprime : ∀ p : ExteriorPrime A,
      f p.val.asIdeal = if (U.j p).val = 0 then χ.character p.val.asIdeal else 0) :
    ∀ I : Ideal (𝓞 F), f I = Detector.deletedPrimitiveIdealCoefficient F χ
      ((A.Sf : Set (HeightOneSpectrum (𝓞 F))) ∪ {v | U.ideal.val ≤ v.asIdeal}) I := by
  classical
  let D : Set (HeightOneSpectrum (𝓞 F)) :=
    (A.Sf : Set (HeightOneSpectrum (𝓞 F))) ∪ {v | U.ideal.val ≤ v.asIdeal}
  let g : Ideal (𝓞 F) → ℂ := Detector.deletedPrimitiveIdealCoefficient F χ D
  have hdelete (v : HeightOneSpectrum (𝓞 F)) :
      (∃ w ∈ D, v.asIdeal ≤ w.asIdeal) ↔ v ∈ D := by
    constructor
    · rintro ⟨w, hw, hvw⟩
      have he : v = w := HeightOneSpectrum.ext
        (v.isMaximal.eq_of_le w.isPrime.ne_top hvw)
      simpa [he] using hw
    · intro hv
      exact ⟨v, hv, le_rfl⟩
  have hgprime (v : HeightOneSpectrum (𝓞 F)) :
      g v.asIdeal = if v ∈ D then 0 else χ.character v.asIdeal := by
    simp only [g, Detector.deletedPrimitiveIdealCoefficient, hdelete]
  have hexterior (v : HeightOneSpectrum (𝓞 F)) :
      v.asIdeal ⊔ A.cS = ⊤ ↔ v ∉ A.Sf := by
    constructor
    · intro h hv
      have hc : A.cS ≤ v.asIdeal :=
        v.isPrime.prod_le.mpr ⟨v, hv, le_rfl⟩
      exact v.isPrime.ne_top (top_le_iff.mp (h ▸ sup_le le_rfl hc))
    · intro hv
      by_contra hn
      have he : v.asIdeal = v.asIdeal ⊔ A.cS :=
        v.isMaximal.eq_of_le hn le_sup_left
      have hc : A.cS ≤ v.asIdeal := le_sup_right.trans_eq he.symm
      obtain ⟨w, hw, hwv⟩ := v.isPrime.prod_le.mp hc
      exact hv ((HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hwv)) ▸ hw)
  have hprimes (v : HeightOneSpectrum (𝓞 F)) : f v.asIdeal = g v.asIdeal := by
    by_cases hv : v ∈ A.Sf
    · rw [houtside v.asIdeal (by simpa [v.ne_bot] using (hexterior v).not.mpr (by simpa using hv)),
        hgprime]
      simp [D, hv]
    · let p : ExteriorPrime A := ⟨v, (hexterior v).mpr hv⟩
      have hj : (U.j p).val = 0 ↔ ¬ U.ideal.val ≤ v.asIdeal := by
        change idealPrimeExponent v.asIdeal U.ideal.val = 0 ↔ _
        rw [idealPrimeExponent, Multiset.count_eq_zero,
          Ideal.mem_normalizedFactors_iff U.ideal.property.1]
        simp [v.isPrime]
      rw [hprime p, hgprime]
      by_cases hd : U.ideal.val ≤ v.asIdeal
      · simp [D, hv, hd, hj.not.mpr (by simpa using hd)]
      · simp [D, hv, hd, hj.mpr hd, p]
  have hgmul (I J : Ideal (𝓞 F)) : g (I * J) = g I * g J := by
    have hd : (∃ v ∈ D, I * J ≤ v.asIdeal) ↔
        (∃ v ∈ D, I ≤ v.asIdeal) ∨ (∃ v ∈ D, J ≤ v.asIdeal) := by
      constructor
      · rintro ⟨v, hv, hIJ⟩
        exact (v.isPrime.mul_le.mp hIJ).elim
          (fun h => Or.inl ⟨v, hv, h⟩) (fun h => Or.inr ⟨v, hv, h⟩)
      · rintro (⟨v, hv, hI⟩ | ⟨v, hv, hJ⟩)
        · exact ⟨v, hv, Ideal.mul_le_left.trans hI⟩
        · exact ⟨v, hv, Ideal.mul_le_right.trans hJ⟩
    simp only [g, Detector.deletedPrimitiveIdealCoefficient, hd]
    split_ifs <;> simp_all [RayClassCharacter.map_mul']
  intro I
  change f I = g I
  refine WfDvdMonoid.induction_on_irreducible (motive := fun I => f I = g I) I ?_ ?_ ?_
  · have hf0 : f ⊥ = 0 := houtside ⊥ (by simp)
    change f ⊥ = g ⊥
    rw [hf0]
    simp [g, Detector.deletedPrimitiveIdealCoefficient,
      (χ.character.eq_zero_iff' ⊥).mpr (Or.inl rfl)]
  · intro I hI
    have he : I = ⊤ := Ideal.isUnit_iff.mp hI
    subst I
    rw [hone]
    have hd : ¬ ∃ v ∈ D, (⊤ : Ideal (𝓞 F)) ≤ v.asIdeal := by
      rintro ⟨v, _, hv⟩
      exact v.isPrime.ne_top (top_le_iff.mp hv)
    simp only [g, Detector.deletedPrimitiveIdealCoefficient, if_neg hd,
      RayClassCharacter.map_top']
  · intro J p hJ hp hInd
    let v : HeightOneSpectrum (𝓞 F) :=
      ⟨p, Ideal.isPrime_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp),
        (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp).ne_zero⟩
    change f (p * J) = g (p * J)
    rw [hmul, hgmul, hInd, hprimes v]

 def rawPlusCoefficient (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (I : Ideal (𝓞 F)) : ℂ :=
  if hI : I ≠ ⊥ ∧ I ⊔ A.cS = ⊤ then
    AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U ⟨I, hI⟩ else 0

 def rawMinusCoefficient (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (I : Ideal (𝓞 F)) : ℂ :=
  η I * star (rawPlusCoefficient σ U I)

private theorem exterior_mul_iff (I J : Ideal (𝓞 F)) :
    (I * J ≠ ⊥ ∧ I * J ⊔ A.cS = ⊤) ↔
      (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) ∧ (J ≠ ⊥ ∧ J ⊔ A.cS = ⊤) := by
  constructor
  · intro h
    have hI : I ⊔ A.cS = ⊤ := top_unique (by
      rw [← h.2]; exact sup_le_sup_right Ideal.mul_le_left _)
    have hJ : J ⊔ A.cS = ⊤ := top_unique (by
      rw [← h.2]; exact sup_le_sup_right Ideal.mul_le_right _)
    exact ⟨⟨left_ne_zero_of_mul h.1, hI⟩, right_ne_zero_of_mul h.1, hJ⟩
  · rintro ⟨hI, hJ⟩
    refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
    rw [Ideal.mul_sup_eq_of_coprime_left hI.2]
    exact hJ.2

private theorem raw_plus_ext_mul (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (I J : A.Exterior) :
    AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U (ExteriorIdealEuler.mul I J) =
      AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U I *
        AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U J := by
  have hb : ∀ K : A.Exterior,
      AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U K =
        σ (A.sexticResidue K U.u) := fun K =>
    AllRowEuler.UnitCovariance.residueCoefficient_eq (σ := σ) K U.u
  rw [hb, hb, hb,
    show A.sexticResidue (ExteriorIdealEuler.mul I J) U.u =
      A.sexticResidue I U.u * A.sexticResidue J U.u from
      A.sexticResidueFamily_normalized.2.2 I J _ rfl U.u,
    map_mul]

private theorem raw_plus_mul (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (I J : Ideal (𝓞 F)) :
    rawPlusCoefficient σ U (I * J) = rawPlusCoefficient σ U I * rawPlusCoefficient σ U J := by
  have he := exterior_mul_iff (A := A) I J
  unfold rawPlusCoefficient
  by_cases hI : I ≠ ⊥ ∧ I ⊔ A.cS = ⊤
  · by_cases hJ : J ≠ ⊥ ∧ J ⊔ A.cS = ⊤
    · rw [dif_pos (he.mpr ⟨hI, hJ⟩), dif_pos hI, dif_pos hJ]
      exact raw_plus_ext_mul σ U ⟨I, hI⟩ ⟨J, hJ⟩
    · rw [dif_neg (fun h => hJ (he.mp h).2), dif_pos hI, dif_neg hJ, mul_zero]
  · rw [dif_neg (fun h => hI (he.mp h).1), dif_neg hI, zero_mul]

private theorem raw_minus_mul (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (I J : Ideal (𝓞 F)) :
    rawMinusCoefficient σ η U (I * J) =
      rawMinusCoefficient σ η U I * rawMinusCoefficient σ η U J := by
  unfold rawMinusCoefficient
  rw [raw_plus_mul, RayClassCharacter.map_mul', star_mul]
  ring

private theorem raw_plus_one (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) :
    rawPlusCoefficient σ U ⊤ = 1 := by
  have h := (AllRowEuler.InitialSeparation.raw_plus_isCoefficient (σ := σ) U).map_one
  simpa [rawPlusCoefficient, ExteriorIdealEuler.one] using h

private theorem raw_minus_one (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) :
    rawMinusCoefficient σ η U ⊤ = 1 := by
  unfold rawMinusCoefficient
  rw [raw_plus_one, star_one, RayClassCharacter.map_top', mul_one]

private theorem raw_plus_prime_value
    (C : A.GeneralArithmeticContext σ η' hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (χ ψ : Detector.PrimitiveFrequencyCharacter F)
    (hχ : Detector.IsKummerFrequencyCharacter F A.zeta12 σ
      (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
      (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) χ)
    (hψ : Detector.conductorSupportedOn F (rawDeletionSet U) ψ)
    (htwist : ∀ J : Ideal (𝓞 F), J ≠ ⊥ →
      J ⊔ (A.modulus * χ.conductor * ψ.conductor) = ⊤ →
      ψ.character J = η' J * star (χ.character J))
    (p : ExteriorPrime A) :
    rawPlusCoefficient σ U p.val.asIdeal =
      if (U.j p).val = 0 then χ.character p.val.asIdeal else 0 := by
  by_cases hp : (U.j p).val = 0
  · rw [if_pos hp]
    have h := (raw_exterior_prime_identification C U χ ψ hχ hψ htwist p hp).2.1
    unfold rawPlusCoefficient
    rw [dif_pos ⟨p.val.ne_bot, p.property⟩]
    exact h
  · rw [if_neg hp]
    have h := (raw_coefficients_zero_at_frequency_primes C U p hp).1
    unfold rawPlusCoefficient
    rw [dif_pos ⟨p.val.ne_bot, p.property⟩]
    exact h

private theorem raw_minus_prime_value
    (C : A.GeneralArithmeticContext σ η' hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (χ ψ : Detector.PrimitiveFrequencyCharacter F)
    (hχ : Detector.IsKummerFrequencyCharacter F A.zeta12 σ
      (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
      (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) χ)
    (hψ : Detector.conductorSupportedOn F (rawDeletionSet U) ψ)
    (htwist : ∀ J : Ideal (𝓞 F), J ≠ ⊥ →
      J ⊔ (A.modulus * χ.conductor * ψ.conductor) = ⊤ →
      ψ.character J = η' J * star (χ.character J))
    (p : ExteriorPrime A) :
    rawMinusCoefficient σ η' U p.val.asIdeal =
      if (U.j p).val = 0 then ψ.character p.val.asIdeal else 0 := by
  by_cases hp : (U.j p).val = 0
  · rw [if_pos hp]
    obtain ⟨⟨hpc, hpp, hpm⟩, -, -⟩ :=
      raw_exterior_prime_identification C U χ ψ hχ hψ htwist p hp
    unfold rawMinusCoefficient
    rw [raw_plus_prime_value C U χ ψ hχ hψ htwist p, if_pos hp]
    exact (htwist p.val.asIdeal p.val.ne_bot (by
      rw [Ideal.sup_mul_eq_of_coprime_right hpp,
        Ideal.sup_mul_eq_of_coprime_right hpc, hpm])).symm
  · rw [if_neg hp]
    unfold rawMinusCoefficient
    rw [raw_plus_prime_value C U χ ψ hχ hψ htwist p, if_neg hp, star_zero, mul_zero]

end Raw

theorem actual_raw_masked_inducers
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val) :
    ∃ (P M : Frequency R → Detector.PrimitiveFrequencyCharacter F),
      (∀ u : Frequency R, (rawDeletionSet (U u)).Finite) ∧
      (∀ (u : Frequency R) (I : R.A.Exterior),
        AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u) I =
          Detector.deletedPrimitiveIdealCoefficient F (P u) (rawDeletionSet (U u)) I.val) ∧
      (∀ (u : Frequency R) (I : R.A.Exterior),
        AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u) I =
          Detector.deletedPrimitiveIdealCoefficient F (M u) (rawDeletionSet (U u)) I.val) := by
  classical
  have key : ∀ u : Frequency R, ∃ (χ ψ : Detector.PrimitiveFrequencyCharacter F),
      (∀ I : R.A.Exterior,
        AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u) I =
          Detector.deletedPrimitiveIdealCoefficient F χ (rawDeletionSet (U u)) I.val) ∧
      (∀ I : R.A.Exterior,
        AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u) I =
          Detector.deletedPrimitiveIdealCoefficient F ψ (rawDeletionSet (U u)) I.val) := by
    intro u
    obtain ⟨χ, hχ, hχS, hχord⟩ :=
      FrequencyCharacterMasks.KummerConductors.kummer_inducer_exists R.A R.σ (U u).ideal (U u).u
        (U u).generates
    obtain ⟨ψ, htwist, hψS, hψord⟩ :=
      FrequencyCharacterMasks.KummerConductors.finite_order_twist_inducer_exists R.A R.target
        (rawDeletionSet (U u)) (Set.subset_union_left) χ hχS 6 (by decide) hχord
    refine ⟨χ, ψ, ?_, ?_⟩
    · intro I
      have hmask := raw_multiplicative_mask_identification (A := R.A) (U u) χ
        (rawPlusCoefficient R.σ (U u)) (raw_plus_one R.σ (U u))
        (raw_plus_mul R.σ (U u))
        (fun I hI => by simp only [rawPlusCoefficient]; exact dif_neg hI)
        (raw_plus_prime_value C (U u) χ ψ hχ hψS htwist)
        I.val
      have hbridge : rawPlusCoefficient R.σ (U u) I.val =
          AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u) I := by
        unfold rawPlusCoefficient
        rw [dif_pos I.property]
        exact congrArg (AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u))
          (Subtype.ext (rfl : (⟨I.val, I.property⟩ : R.A.Exterior).val = I.val))
      rw [← hbridge]
      simpa [rawDeletionSet] using hmask
    · intro I
      have hmask := raw_multiplicative_mask_identification (A := R.A) (U u) ψ
        (rawMinusCoefficient R.σ R.target (U u)) (raw_minus_one R.σ R.target (U u))
        (raw_minus_mul R.σ R.target (U u))
        (fun I hI => by
          unfold rawMinusCoefficient
          rw [show rawPlusCoefficient R.σ (U u) I = 0 from by
            unfold rawPlusCoefficient; exact dif_neg hI]
          rw [star_zero, mul_zero])
        (raw_minus_prime_value C (U u) χ ψ hχ hψS htwist)
        I.val
      have hbridge : rawMinusCoefficient R.σ R.target (U u) I.val =
          AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u) I := by
        unfold rawMinusCoefficient
        rw [show rawPlusCoefficient R.σ (U u) I.val =
          AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u) I from by
            unfold rawPlusCoefficient
            rw [dif_pos I.property]
            exact congrArg (AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u))
              (Subtype.ext (rfl : (⟨I.val, I.property⟩ : R.A.Exterior).val = I.val))]
        rfl
      rw [← hbridge]
      simpa [rawDeletionSet] using hmask
  choose P M hP hM using key
  exact ⟨P, M, fun u => rawDeletionSet_finite (U u), hP, hM⟩

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RawHeckeRows
