module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveCharacterCofiniteRigidity
public import DedekindZetaZeroFree.Arithmetic.Kummer.DeletedPrimeCoefficients
public import DedekindZetaZeroFree.ZeroDetection.Conductors.FrequencyRepresentatives
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveInductionConductorSupport

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]

private theorem exterior_prime (A : SArithmeticData F)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    v.asIdeal ⊔ A.cS = ⊤ := by
  apply Ideal.sup_prod_eq_top
  intro w hw
  apply v.isMaximal.coprime_of_ne w.isMaximal
  intro he
  exact hv (IsDedekindDomain.HeightOneSpectrum.ext he ▸ hw)

theorem deleted_primitive_inducers_eq
    (A : SArithmeticData F)
    (D : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (hD : D.Finite)
    (hSf : (A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ⊆ D)
    (ν ψ : Detector.PrimitiveFrequencyCharacter F)
    (h : ∀ I : A.Exterior,
      Detector.deletedPrimitiveIdealCoefficient F ν D I.val =
        Detector.deletedPrimitiveIdealCoefficient F ψ D I.val) :
    ν = ψ := by
  classical
  haveI htc : NumberField.IsTotallyComplex F :=
    primitive12_totallyComplex F A.zeta12 A.primitive_zeta12
  refine primitive_inducers_eq_of_cofinite_prime_values (F := F) ν ψ ?_
  rw [Filter.eventually_cofinite]
  refine hD.subset ?_
  intro v hv
  by_contra hvD
  have hvSf : v ∉ A.Sf := fun hmem => hvD (hSf (by simpa using hmem))
  have hcop : v.asIdeal ⊔ A.cS = ⊤ := exterior_prime A v hvSf

  have hnot : ¬ (∃ w ∈ D, v.asIdeal ≤ w.asIdeal) := by
    rintro ⟨w, hwD, hle⟩
    exact hvD (IsDedekindDomain.HeightOneSpectrum.ext
      (v.isMaximal.eq_of_le w.isMaximal.ne_top hle) ▸ hwD)
  have hν : Detector.deletedPrimitiveIdealCoefficient F ν D v.asIdeal =
      ν.character v.asIdeal := by
    unfold Detector.deletedPrimitiveIdealCoefficient
    rw [if_neg hnot]
  have hψ : Detector.deletedPrimitiveIdealCoefficient F ψ D v.asIdeal =
      ψ.character v.asIdeal := by
    unfold Detector.deletedPrimitiveIdealCoefficient
    rw [if_neg hnot]
  have hI := h ⟨v.asIdeal, v.ne_bot, hcop⟩
  exact hv (hν.symm.trans (hI.trans hψ))

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.DeletedCoefficient
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]

private theorem exterior_mul_iff (A : SArithmeticData F) (I J : Ideal (𝓞 F)) :
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

 def plusCoeff (A : SArithmeticData F) (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (I : Ideal (𝓞 F)) : ℂ :=
  if hI : I ≠ ⊥ ∧ I ⊔ A.cS = ⊤ then
    AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U ⟨I, hI⟩ else 0

private theorem plusCoeff_ext_mul (A : SArithmeticData F) (σ : F →+* ℂ)
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

private theorem plusCoeff_mul (A : SArithmeticData F) (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (I J : Ideal (𝓞 F)) :
    plusCoeff A σ U (I * J) = plusCoeff A σ U I * plusCoeff A σ U J := by
  have he := exterior_mul_iff A I J
  unfold plusCoeff
  by_cases hI : I ≠ ⊥ ∧ I ⊔ A.cS = ⊤
  · by_cases hJ : J ≠ ⊥ ∧ J ⊔ A.cS = ⊤
    · rw [dif_pos (he.mpr ⟨hI, hJ⟩), dif_pos hI, dif_pos hJ]
      exact plusCoeff_ext_mul A σ U ⟨I, hI⟩ ⟨J, hJ⟩
    · rw [dif_neg (fun h => hJ (he.mp h).2), dif_pos hI, dif_neg hJ, mul_zero]
  · rw [dif_neg (fun h => hI (he.mp h).1), dif_neg hI, zero_mul]

private theorem plusCoeff_one (A : SArithmeticData F) (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) : plusCoeff A σ U ⊤ = 1 := by
  have h := (AllRowEuler.InitialSeparation.raw_plus_isCoefficient (σ := σ) U).map_one
  simpa [plusCoeff, ExteriorIdealEuler.one] using h

private theorem plusCoeff_mask (A : SArithmeticData F) (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (χ : Detector.PrimitiveFrequencyCharacter F)
    (hprime : ∀ p : ExteriorPrime A,
      AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U (primeIdeal p) =
      if U.ideal.val ≤ p.val.asIdeal then 0 else χ.character p.val.asIdeal) :
    ∀ I : Ideal (𝓞 F), plusCoeff A σ U I =
      Detector.deletedPrimitiveIdealCoefficient F χ
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
  have hprimes (v : HeightOneSpectrum (𝓞 F)) : plusCoeff A σ U v.asIdeal = g v.asIdeal := by
    by_cases hv : v ∈ A.Sf
    · have hout : ¬ (v.asIdeal ≠ ⊥ ∧ v.asIdeal ⊔ A.cS = ⊤) := by
        simpa [v.ne_bot] using (hexterior v).not.mpr (by simpa using hv)
      rw [show plusCoeff A σ U v.asIdeal = 0 from by
        unfold plusCoeff
        exact dif_neg hout, hgprime]
      simp [D, hv]
    · let p : ExteriorPrime A := ⟨v, (hexterior v).mpr hv⟩
      have hbridge : plusCoeff A σ U v.asIdeal =
          AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U (primeIdeal p) := by
        unfold plusCoeff
        rw [dif_pos ⟨v.ne_bot, (hexterior v).mpr hv⟩]
        exact congrArg (AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U)
          (Subtype.ext rfl)
      have hpv : p.val.asIdeal = v.asIdeal := rfl
      have hmem : v ∈ D ↔ U.ideal.val ≤ v.asIdeal := by
        unfold D
        rw [Set.mem_union]
        simp [hv]
      rw [hbridge, hprime p, hgprime]
      by_cases hd : U.ideal.val ≤ v.asIdeal
      · rw [if_pos (by rwa [hpv]), if_pos (hmem.mpr hd)]
      · rw [if_neg (by rwa [hpv]), if_neg (fun h => hd (hmem.mp h))]
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
  change plusCoeff A σ U I = g I
  refine WfDvdMonoid.induction_on_irreducible (motive := fun I => plusCoeff A σ U I = g I)
    I ?_ ?_ ?_
  · have hf0 : plusCoeff A σ U ⊥ = 0 := by
      unfold plusCoeff
      exact dif_neg (by simp)
    change plusCoeff A σ U ⊥ = g ⊥
    rw [hf0]
    simp [g, Detector.deletedPrimitiveIdealCoefficient,
      (χ.character.eq_zero_iff' ⊥).mpr (Or.inl rfl)]
  · intro I hI
    have he : I = ⊤ := Ideal.isUnit_iff.mp hI
    subst I
    rw [plusCoeff_one A σ U]
    have hd : ¬ ∃ v ∈ D, (⊤ : Ideal (𝓞 F)) ≤ v.asIdeal := by
      rintro ⟨v, _, hv⟩
      exact v.isPrime.ne_top (top_le_iff.mp hv)
    simp only [g, Detector.deletedPrimitiveIdealCoefficient, if_neg hd,
      RayClassCharacter.map_top']
  · intro J p hJ hp hInd
    let v : HeightOneSpectrum (𝓞 F) :=
      ⟨p, Ideal.isPrime_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp),
        (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp).ne_zero⟩
    change plusCoeff A σ U (p * J) = g (p * J)
    rw [plusCoeff_mul, hgmul, hInd, hprimes v]

theorem plus_coefficient_of_prime_values
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (χ : Detector.PrimitiveFrequencyCharacter F)
    (hprime : ∀ p : LocalFiniteSums.ExteriorPrime A,
      AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U
        (LocalFiniteSums.primeIdeal p) =
      if U.ideal.val ≤ p.val.asIdeal then 0 else χ.character p.val.asIdeal)
    (I : A.Exterior)
    (hI : ¬ ∃ v ∈ RawHeckeRows.rawDeletionSet U, I.val ≤ v.asIdeal) :
    AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U I =
      χ.character I.val := by
  have hmask := plusCoeff_mask A σ U χ hprime I.val
  have hbridge : plusCoeff A σ U I.val =
      AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U I := by
    unfold plusCoeff
    rw [dif_pos I.property]
    exact congrArg (AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U)
      (Subtype.ext (rfl : (⟨I.val, I.property⟩ : A.Exterior).val = I.val))
  rw [← hbridge, hmask]
  unfold Detector.deletedPrimitiveIdealCoefficient
  rw [if_neg (by simpa [RawHeckeRows.rawDeletionSet] using hI)]

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.DeletedCoefficient

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.DeletedCoefficient
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]

theorem twist_conductor_supported
    (D : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (η0 χ ψ : Detector.PrimitiveFrequencyCharacter F)
    (hη0 : Detector.conductorSupportedOn F D η0)
    (hχ : Detector.conductorSupportedOn F D χ)
    (htwist : Detector.IsPrimitiveFrequencyTwist F η0 χ ψ) :
    Detector.conductorSupportedOn F D ψ := by
  intro v hv
  have hprod : η0.conductor * χ.conductor ≤ ψ.conductor :=
    Detector.finite_mask_twist_conductor_le F η0 χ ψ htwist
  have hle : η0.conductor * χ.conductor ≤ v.asIdeal := le_trans hprod hv
  rcases (Ideal.IsPrime.mul_le v.isPrime).mp hle with h | h
  · exact hη0 v h
  · exact hχ v h

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.DeletedCoefficient

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]

private theorem coprime_of_avoiding_support
    (D : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (I m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (hsupport : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      m ≤ v.asIdeal → v ∈ D)
    (havoid : ¬ ∃ v ∈ D, I ≤ v.asIdeal) : I ⊔ m = ⊤ := by
  by_contra hn
  obtain ⟨p, hp, hpm⟩ := Ideal.exists_le_maximal (I ⊔ m) hn
  have hp0 : p ≠ ⊥ := by
    intro he
    exact hm (le_bot_iff.mp (le_sup_right.trans (hpm.trans_eq he)))
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨p, hp.isPrime, hp0⟩
  exact havoid ⟨v, hsupport v (le_sup_right.trans hpm), le_sup_left.trans hpm⟩

private theorem plus_zero_at_common_frequency_prime
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (I : A.Exterior)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hIv : I.val ≤ v.asIdeal) (hUv : U.ideal.val ≤ v.asIdeal) :
    AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U I = 0 := by
  have hvS : v.asIdeal ⊔ A.cS = ⊤ :=
    top_unique (I.property.2 ▸ sup_le_sup_right hIv A.cS)
  let p : LocalFiniteSums.ExteriorPrime A := ⟨v, hvS⟩
  let P := LocalFiniteSums.primeIdeal p
  letI : Nontrivial (A.R ⧸ A.extendIdeal P) :=
    Ideal.Quotient.nontrivial_iff.mpr (A.residue_extendIdeal_ne_top P v.isPrime.ne_top)
  have hu : U.u ∈ A.extendIdeal P := by
    have hmem : U.u ∈ Ideal.span {U.u} := Ideal.mem_span_singleton_self _
    rw [U.generates.2] at hmem
    exact Ideal.map_mono hUv hmem
  have hz : Ideal.Quotient.mk (A.extendIdeal P) U.u = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hu
  have hnonunit : ¬ IsUnit (Ideal.Quotient.mk (A.extendIdeal I) U.u) := by
    intro hunit
    have hle : A.extendIdeal I ≤ A.extendIdeal P := Ideal.map_mono hIv
    have hu' := hunit.map (Ideal.Quotient.factor hle)
    rw [Ideal.Quotient.factor_mk, hz] at hu'
    exact not_isUnit_zero hu'
  exact MulChar.map_nonunit _ hnonunit

theorem deleted_raw_minus_of_prime_values
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (η0 χ ψ : Detector.PrimitiveFrequencyCharacter F)
    (hη0 : Detector.conductorSupportedOn F
      (A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) η0)
    (htarget : ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
      I ⊔ (A.modulus * η0.conductor) = ⊤ → η0.character I = η I)
    (hχ : Detector.conductorSupportedOn F (RawHeckeRows.rawDeletionSet U) χ)
    (hprime : ∀ p : LocalFiniteSums.ExteriorPrime A,
      AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U
        (LocalFiniteSums.primeIdeal p) =
      if U.ideal.val ≤ p.val.asIdeal then 0 else χ.character p.val.asIdeal)
    (htwist : Detector.IsPrimitiveFrequencyTwist F η0 χ ψ) :
    ∀ I : A.Exterior,
      AllRowEuler.InitialSeparation.minusExteriorCoefficient σ η U I =
        Detector.deletedPrimitiveIdealCoefficient F ψ
          (RawHeckeRows.rawDeletionSet U) I.val := by
  have hηD : Detector.conductorSupportedOn F (RawHeckeRows.rawDeletionSet U) η0 :=
    fun v hv => Or.inl (hη0 v hv)
  have hψ := DeletedCoefficient.twist_conductor_supported
    (RawHeckeRows.rawDeletionSet U) η0 χ ψ hηD hχ htwist
  intro I
  unfold Detector.deletedPrimitiveIdealCoefficient
  by_cases hD : ∃ v ∈ RawHeckeRows.rawDeletionSet U, I.val ≤ v.asIdeal
  · rw [if_pos hD]
    obtain ⟨v, hv, hIv⟩ := hD
    rcases hv with hvS | hUv
    · have hcop := (A.exterior_iff ⟨I.val, I.property.1⟩).mp I.property.2 v hvS
      have htop : v.asIdeal = ⊤ := top_unique (hcop ▸ sup_le hIv le_rfl)
      exact (v.isPrime.ne_top htop).elim
    · rw [AllRowEuler.InitialSeparation.minusExteriorCoefficient,
        plus_zero_at_common_frequency_prime A σ U I v hIv hUv, star_zero, mul_zero]
  · rw [if_neg hD]
    have hm : I.val ⊔ A.modulus = ⊤ :=
      coprime_of_avoiding_support (RawHeckeRows.rawDeletionSet U)
        I.val A.modulus A.modulus_ne_zero (fun v hv => Or.inl (A.modulus_support v hv)) hD
    have hη : I.val ⊔ η0.conductor = ⊤ :=
      coprime_of_avoiding_support (RawHeckeRows.rawDeletionSet U)
        I.val η0.conductor η0.conductor_ne_zero hηD hD
    have hc : I.val ⊔ χ.conductor = ⊤ :=
      coprime_of_avoiding_support (RawHeckeRows.rawDeletionSet U)
        I.val χ.conductor χ.conductor_ne_zero hχ hD
    have hp : I.val ⊔ ψ.conductor = ⊤ :=
      coprime_of_avoiding_support (RawHeckeRows.rawDeletionSet U)
        I.val ψ.conductor ψ.conductor_ne_zero hψ hD
    have hηeq := htarget I.val I.property.1 (by
      rw [Ideal.sup_mul_eq_of_coprime_right hη, hm])
    have hψeq := htwist I.val I.property.1 (by
      rw [Ideal.sup_mul_eq_of_coprime_right hp,
        Ideal.sup_mul_eq_of_coprime_right hc, hη])
    rw [AllRowEuler.InitialSeparation.minusExteriorCoefficient,
      DeletedCoefficient.plus_coefficient_of_prime_values A σ U χ hprime I hD]
    simpa only [hηeq, starRingEnd_apply] using hψeq.symm

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem raw_minus_family_identification
    (R : PrincipalMellin.ActualRecipe S η)
    (V : Detector.FrequencyRepresentatives F
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))))
    (e : Frequency R ≃ V.carrier)
    (he : ∀ u : Frequency R, (e u).val = ThetaReflectionData.rowUnit R.A u.val)
    (K : Detector.KummerFrequencyFamily F R.A.zeta12 R.σ
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) V)
    (η0 : Detector.PrimitiveFrequencyCharacter F)
    (hη0 : Detector.conductorSupportedOn F
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) η0)
    (htarget : ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
      I ⊔ (R.A.modulus * η0.conductor) = ⊤ → η0.character I = R.target I) :
    ∃ T : Detector.TwistedFrequencyFamily F R.A.zeta12 R.σ
        (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) V K η0,
        ∀ (u : Frequency R) (U : AllRowEuler.InitialSeparation.RawFrequency R.A),
          U.u = u.val.val → ∀ I : R.A.Exterior,
            AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target U I =
              Detector.deletedPrimitiveIdealCoefficient F (T.denominator (e u))
                (RawHeckeRows.rawDeletionSet U) I.val := by
  classical
  letI : IsPrincipalIdealRing R.A.R :=
    R.A.principalIdealRing_of_classGroup_subsingleton R.classKilled
  have hSix : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 →
        v ∈ (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) := by
    intro v hv
    by_contra hout
    exact hv (ArithmeticContext.actual_outside_norm_coprime_six R.A v hout)
  obtain ⟨T⟩ := Detector.twisted_frequency_family_exists F R.A.zeta12
    R.A.primitive_zeta12 R.σ (R.A.Sf : Set _) R.A.Sf.finite_toSet hSix V K η0
  refine ⟨T, ?_⟩
  intro u U hU
  have hunit : (e u).val =
      Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1) := by
    rw [he u]
    apply Units.ext
    change (u.val.val : F) = (U.u : F)
    rw [hU]
  have hK : Detector.IsKummerFrequencyCharacter F R.A.zeta12 R.σ
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
      (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1))
      (K.numerator (e u)) := by
    rw [← hunit]
    exact K.kummer (e u)
  obtain ⟨hχ, hprime⟩ := source_kummer_raw_prime_values R.A R.σ U
    (K.numerator (e u)) hK
  exact deleted_raw_minus_of_prime_values R.A R.σ R.target U η0
    (K.numerator (e u)) (T.denominator (e u)) hη0 htarget hχ hprime
    (T.induces (e u))

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem actual_raw_minus_inducer_conductor_bound
    (R : PrincipalMellin.ActualRecipe S η) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (u : Frequency R) (U : AllRowEuler.InitialSeparation.RawFrequency R.A),
        U.u = u.val.val → ∀ ν : Detector.PrimitiveFrequencyCharacter F,
        (∀ I : R.A.Exterior,
          AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target U I =
            Detector.deletedPrimitiveIdealCoefficient F ν
              (RawHeckeRows.rawDeletionSet U) I.val) →
        (Ideal.absNorm ν.conductor : ℝ) ≤ c * frequencyNorm R u := by
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
  obtain ⟨c, hc, hbound⟩ := Detector.frequency_denominator_conductor_bound F
    R.A.zeta12 R.A.primitive_zeta12 R.σ (R.A.Sf : Set _)
    R.A.Sf.finite_toSet hSix η0 hη0
  refine ⟨c, hc, ?_⟩
  intro u U hU ν hν
  have hD : (RawHeckeRows.rawDeletionSet U).Finite := by
    unfold RawHeckeRows.rawDeletionSet
    apply Set.Finite.union R.A.Sf.finite_toSet
    let s : Finset (Ideal (𝓞 F)) :=
      (UniqueFactorizationMonoid.normalizedFactors U.ideal.val).toFinset
    have hinj : Function.Injective
        (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => v.asIdeal) :=
      IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
    have hsub : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) | U.ideal.val ≤ v.asIdeal} ⊆
        (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => v.asIdeal) ⁻¹'
          (↑s : Set (Ideal (𝓞 F))) := by
      intro v hv
      simp only [Set.mem_preimage, Finset.mem_coe]
      exact Multiset.mem_toFinset.mpr
        ((Ideal.mem_normalizedFactors_iff U.ideal.property.1).mpr ⟨v.isPrime, hv⟩)
    exact (s.finite_toSet.preimage hinj.injOn).subset hsub
  have hEq : ν = T.denominator (e u) :=
    MinusArithmetic.deleted_primitive_inducers_eq R.A
      (RawHeckeRows.rawDeletionSet U) hD Set.subset_union_left
      ν (T.denominator (e u)) (fun I => (hν I).symm.trans (hT u U hU I))
  rw [hEq, ← hnorm u]
  exact hbound V K T (e u)

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads

end
