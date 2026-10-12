module

public import DedekindZetaZeroFree.Moments.Principal.Corrections.Definitions
public import DedekindZetaZeroFree.LFunctions.Hecke.FiniteEulerDeletion
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.PrincipalSexticCharacter

@[expose] public section

section

open scoped NumberField Classical
open IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.FrequencyCharacterMasks.KummerConductors
set_option autoImplicit false

theorem kummer_norm_conductor_prime_absent {F : Type} [Field F] [NumberField F]
    (n : ℕ+) (hn : (n : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty) (u : Fˣ)
    (v : HeightOneSpectrum (𝓞 F))
    (hu : v.valuation F (u : F) = 1) (hv : v.valuation F (n : F) = 1) :
    let E := KummerTheory.chosenSimpleKummerExtension F n hn u
    letI := KummerTheory.chosenSimpleKummerExtension_finiteDimensional F n hn u
    letI := KummerTheory.chosenSimpleKummerExtension_isAbelianGalois F n hn hmu u
    letI := NumberField.of_module_finite F E
    v ∉ (ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus F E).finitePart.support := by
  let E := KummerTheory.chosenSimpleKummerExtension F n hn u
  letI := KummerTheory.chosenSimpleKummerExtension_finiteDimensional F n hn u
  letI := KummerTheory.chosenSimpleKummerExtension_isAbelianGalois F n hn hmu u
  letI := NumberField.of_module_finite F E
  dsimp only
  intro h
  exact GlobalClassFieldTheory.GlobalClassFields.mem_ideleClassNorm_narrowFiniteConductor_support_imp_chosenFinitePlace_ramified v h
    (KummerTheory.chosenSimpleKummerExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one n hn hmu u v hu hv)

theorem sextic_norm_conductor_support {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (I : A.Exterior) (u : A.R) (hu : A.Generates I u) :
    let hn : (6 : F) ≠ 0 := by norm_num
    let a := Units.mk0 (u : F) (by exact_mod_cast hu.1)
    let E := KummerTheory.chosenSimpleKummerExtension F (6 : ℕ+) hn a
    letI := KummerTheory.chosenSimpleKummerExtension_finiteDimensional F (6 : ℕ+) hn a
    letI := KummerTheory.chosenSimpleKummerExtension_isAbelianGalois F (6 : ℕ+) hn
      A.primitive_sixth_root a
    letI := NumberField.of_module_finite F E
    ↑(ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus F E).finitePart.support ⊆
      ((A.Sf : Set (HeightOneSpectrum (𝓞 F))) ∪ {v | I.val ≤ v.asIdeal}) := by
  let hn : (6 : F) ≠ 0 := by norm_num
  let a := Units.mk0 (u : F) (by exact_mod_cast hu.1)
  let E := KummerTheory.chosenSimpleKummerExtension F (6 : ℕ+) hn a
  letI := KummerTheory.chosenSimpleKummerExtension_finiteDimensional F (6 : ℕ+) hn a
  letI := KummerTheory.chosenSimpleKummerExtension_isAbelianGalois F (6 : ℕ+) hn A.primitive_sixth_root a
  letI := NumberField.of_module_finite F E
  dsimp only
  intro v hv
  by_cases hvS : v ∈ A.Sf
  · exact Or.inl hvS
  · right
    by_contra hI
    have hval := ArithmeticContext.actual_generator_valuation_unit A I u a hu rfl v hvS hI
    have hsix : v.valuation F (6 : F) = 1 := by
      convert (v.valuation_eq_one_iff_notMem (K := F) (r := (6 : 𝓞 F))).2
        (fun h => hvS (A.above_six v h)) using 1 <;> norm_cast
    exact kummer_norm_conductor_prime_absent (6 : ℕ+) hn A.primitive_sixth_root a v hval hsix hv

private theorem kummer_conductor_support {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (σ : F →+* ℂ) (I : A.Exterior)
    (u : A.R) (hu : A.Generates I u)
    (χ : Detector.PrimitiveFrequencyCharacter F)
    (hχ : Detector.IsKummerFrequencyCharacter F A.zeta12 σ
      (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
      (Units.mk0 (u : F) (by exact_mod_cast hu.1)) χ) :
    Detector.conductorSupportedOn F
      ((A.Sf : Set (HeightOneSpectrum (𝓞 F))) ∪ {v | I.val ≤ v.asIdeal}) χ := by
  intro v hv
  by_cases hvS : v ∈ A.Sf
  · exact Or.inl hvS
  · right
    by_contra hnot
    have hvu := ArithmeticContext.actual_generator_valuation_unit A I u
      (Units.mk0 (u : F) (by exact_mod_cast hu.1)) hu rfl v hvS hnot
    have hcop := (hχ v hvS hvu).1
    have : v.asIdeal = ⊤ := by simpa [sup_eq_left.mpr hv] using hcop
    exact v.isPrime.ne_top this

theorem kummer_inducer_exists {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (σ : F →+* ℂ) (I : A.Exterior)
    (u : A.R) (hu : A.Generates I u) :
    ∃ χ : Detector.PrimitiveFrequencyCharacter F,
      Detector.IsKummerFrequencyCharacter F A.zeta12 σ
        (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (Units.mk0 (u : F) (by exact_mod_cast hu.1)) χ ∧
      Detector.conductorSupportedOn F
        ((A.Sf : Set (HeightOneSpectrum (𝓞 F))) ∪ {v | I.val ≤ v.asIdeal}) χ ∧
      (∀ J : Ideal (𝓞 F), J ≠ ⊥ → J ⊔ χ.conductor = ⊤ →
        χ.character J ^ (6 : ℕ) = 1) := by
  obtain ⟨χ, hχ⟩ : ∃ χ : Detector.PrimitiveFrequencyCharacter F,
      Detector.IsKummerFrequencyCharacter F A.zeta12 σ
        (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (Units.mk0 (u : F) (by exact_mod_cast hu.1)) χ := by
    let a := Units.mk0 (u : F) (by exact_mod_cast hu.1)
    let hc := primitive12_totallyComplex F A.zeta12 A.primitive_zeta12
    obtain ⟨m, hm, ρ, χ, hp, _, _, hχ, _⟩ := PrimitiveRay.primitiveRay_exists hc
      (PrimitiveRay.arithmeticSexticArtinCharacter A.zeta12 A.primitive_zeta12 σ a)
      ⟨6, by norm_num, PrimitiveRay.arithmeticSexticArtinCharacter_pow_six A.zeta12 A.primitive_zeta12 σ a⟩
    refine ⟨⟨m, hm, χ, hp⟩, ?_⟩
    intro v hv hu
    have hSix : (Ideal.absNorm v.asIdeal).Coprime 6 := by
      have hmod := A.exterior_norm_mod_twelve v hv
      have hmod6 : Ideal.absNorm v.asIdeal % 6 = 1 := by omega
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, hmod6]
      norm_num
    have hn := PrimitiveRay.arithmeticSextic_primitiveRay_support A.zeta12 A.primitive_zeta12 σ a hc m hm χ hp hχ v hSix hu
    have hcop : v.asIdeal ⊔ m = ⊤ := by
      exact v.isMaximal.out.2 _
        (lt_of_le_of_ne le_sup_left (fun h => hn (h ▸ le_sup_right)))
    refine ⟨hcop, ?_⟩
    obtain ⟨j, hj, heq⟩ := PrimitiveRay.arithmeticSexticArtinCharacter_prime A.zeta12 A.primitive_zeta12 σ a v hSix hu
    refine ⟨j, hj, ?_⟩
    have hv' : v ∉ (RayClassBridge.narrowIdealModulus F m hm).finitePart.support := by
      simpa only [← Finset.mem_coe, RayClassBridge.narrowIdealModulus_support, Set.mem_setOf_eq] using hn
    rw [← RayClassBridge.ideleClassCharacter_finitePrimeIdele F hc m hm χ v hv', hχ]
    exact heq
  exact ⟨χ, hχ, kummer_conductor_support A σ I u hu χ hχ,
    Detector.Conductor.global_kummer_sixth_power F A.zeta12
      A.primitive_zeta12 σ (A.Sf : Set _) A.Sf.finite_toSet
      (Units.mk0 (u : F) (by exact_mod_cast hu.1)) χ hχ⟩

end DedekindZetaZeroFree.FrequencyCharacterMasks.KummerConductors

end

end

section

open scoped NumberField Classical
open IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.FrequencyCharacterMasks.KummerConductors
set_option autoImplicit false

theorem finite_order_ray {F : Type} [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (η : RayClassCharacter F m) :
    ∃ e : ℕ, 0 < e ∧ ∀ J : Ideal (𝓞 F), J ≠ ⊥ → J ⊔ m = ⊤ → η J ^ e = 1 := by
  let M := RayClassBridge.narrowIdealModulus F m hm
  letI : Finite (ClassFieldTheory.RayClassGroup M) :=
    ClassFieldTheory.rayClassGroup_finite F M
  refine ⟨Nat.card (ClassFieldTheory.RayClassGroup M), Nat.card_pos, ?_⟩
  intro J hJ hcJ
  obtain ⟨_, a, ha, ham, hpos, hspan⟩ :=
    RayUnitary.integral_ideal_pow_card_rayClassGroup_generator F m hm J hJ hcJ
  have hp : ∀ k : ℕ, η (J ^ k) = η J ^ k := by
    intro k
    induction k with
    | zero => simp [η.map_top']
    | succ k ih => rw [pow_succ, η.map_mul', ih, pow_succ]
  rw [← hp, hspan]
  exact η.map_span' a ha ham hpos

 def rawTwist {F : Type} [Field F] [NumberField F]
    (m f : Ideal (𝓞 F)) (η : RayClassCharacter F m) (χ : RayClassCharacter F f) :
    RayClassCharacter F (m * f) where
  toFun J := η J * star (χ J)
  map_mul' I J := by
    rw [η.map_mul', χ.map_mul', star_mul]
    ring
  map_top' := by simp [η.map_top', χ.map_top']
  eq_zero_iff' J := by
    have hc : J ⊔ (m * f) = ⊤ ↔ J ⊔ m = ⊤ ∧ J ⊔ f = ⊤ := by
      simp only [← Ideal.isCoprime_iff_sup_eq, IsCoprime.mul_right_iff]
    simp only [mul_eq_zero, star_eq_zero, η.eq_zero_iff', χ.eq_zero_iff']
    tauto
  map_span' a ha hm hpos := by
    rw [η.map_span' a ha (Ideal.mul_le_left hm) hpos,
      χ.map_span' a ha (Ideal.mul_le_right hm) hpos, star_one, mul_one]

private theorem product_support {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (D : Set (HeightOneSpectrum (𝓞 F)))
    (hD : (A.Sf : Set _) ⊆ D) (χ : Detector.PrimitiveFrequencyCharacter F)
    (hχD : Detector.conductorSupportedOn F D χ)
    (f : Ideal (𝓞 F)) (hf : A.modulus * χ.conductor ≤ f) :
    ∀ v : HeightOneSpectrum (𝓞 F), f ≤ v.asIdeal → v ∈ D := by
  intro v hv
  have hp : A.modulus * χ.conductor ≤ v.asIdeal := hf.trans hv
  rcases v.isPrime.mul_le.mp hp with h | h
  · exact hD (A.modulus_support v h)
  · exact hχD v h

theorem finite_order_twist_inducer_exists {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (η : RayClassCharacter F A.modulus)
    (D : Set (HeightOneSpectrum (𝓞 F))) (hD : (A.Sf : Set _) ⊆ D)
    (χ : Detector.PrimitiveFrequencyCharacter F)
    (hχD : Detector.conductorSupportedOn F D χ)
    (n : ℕ) (hn : 0 < n)
    (hχn : ∀ J : Ideal (𝓞 F), J ≠ ⊥ → J ⊔ χ.conductor = ⊤ →
      χ.character J ^ n = 1) :
    ∃ ψ : Detector.PrimitiveFrequencyCharacter F,
      (∀ J : Ideal (𝓞 F), J ≠ ⊥ →
        J ⊔ (A.modulus * χ.conductor * ψ.conductor) = ⊤ →
        ψ.character J = η J * star (χ.character J)) ∧
      Detector.conductorSupportedOn F D ψ ∧
      (∃ e : ℕ, 0 < e ∧
        ∀ J : Ideal (𝓞 F), J ≠ ⊥ → J ⊔ ψ.conductor = ⊤ →
          ψ.character J ^ e = 1) := by
  let m := A.modulus * χ.conductor
  have hm : m ≠ ⊥ := mul_ne_zero A.modulus_ne_zero χ.conductor_ne_zero
  let τ := rawTwist A.modulus χ.conductor η χ.character
  let hc := primitive12_totallyComplex F A.zeta12 A.primitive_zeta12
  let Φ : IdeleClassGroup F →ₜ* ℂˣ :=
    ⟨RayClassBridge.ideleClassCharacter F hc m hm τ,
      RayClassBridge.ideleClassCharacter_continuous F hc m hm τ⟩
  obtain ⟨f, hf, ρ, ω, hω, _, _, hωΦ, _⟩ :=
    PrimitiveRay.primitiveRay_exists hc Φ
      ⟨Nat.card (ClassFieldTheory.RayClassGroup
        (RayClassBridge.narrowIdealModulus F m hm)),
        RayClassBridge.ideleClassCharacter_exponent_pos F m hm,
        RayClassBridge.ideleClassCharacter_pow_card F hc m hm τ⟩
  let ψ : Detector.PrimitiveFrequencyCharacter F := ⟨f, hf, ω, hω⟩
  refine ⟨ψ, ?_, ?_, finite_order_ray f hf ω⟩
  · intro J hJ hcJ
    have hcm : J ⊔ m = ⊤ :=
      top_unique (hcJ ▸ sup_le_sup_left (Ideal.mul_le_left : m * f ≤ m) J)
    have hcf : J ⊔ f = ⊤ :=
      top_unique (hcJ ▸ sup_le_sup_left (Ideal.mul_le_right : m * f ≤ f) J)
    have hid := congrArg (fun z : ℂˣ => (z : ℂ))
      (hωΦ (QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
        (RayClassBridge.idealIdele F J hJ)))
    change (RayClassBridge.ideleClassCharacter F hc f hf ω
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
        (RayClassBridge.idealIdele F J hJ)) : ℂ) =
      (RayClassBridge.ideleClassCharacter F hc m hm τ
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
        (RayClassBridge.idealIdele F J hJ)) : ℂ) at hid
    change ω J = τ J
    simpa only [RayClassBridge.ideleClassCharacter_idealIdele F hc f hf ω J hJ hcf,
      RayClassBridge.ideleClassCharacter_idealIdele F hc m hm τ J hJ hcm] using hid
  · intro v hv
    by_contra hvD
    have hnot : ¬ m ≤ v.asIdeal := by
      intro h
      exact hvD (product_support A D hD χ hχD m le_rfl v h)
    exact PrimitiveRay.primitiveRay_support hc Φ f hf ω hω hωΦ v
      (fun t ht => RayClassBridge.ideleClassCharacter_finitePlaceIdeleClass_unit_of_not_dvd
        F hc m hm τ v hnot t ht) hv

end DedekindZetaZeroFree.FrequencyCharacterMasks.KummerConductors

end

end

section

open scoped NumberField Classical
open IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.FrequencyCharacterMasks.KummerConductors
set_option autoImplicit false

open LocalFiniteSums CorrectionFactors

theorem exterior_prime_identification {F : Type} [Field F] [NumberField F]
    {A : SArithmeticData F} {σ : F →+* ℂ}
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
    {C : A.GeneralArithmeticContext σ η hS}
    (U : Frequency C) (χ ψ : Detector.PrimitiveFrequencyCharacter F)
    (hχ : Detector.IsKummerFrequencyCharacter F A.zeta12 σ
      (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
      (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) χ)
    (hψ : Detector.conductorSupportedOn F
      ((A.Sf : Set (HeightOneSpectrum (𝓞 F))) ∪ {v | U.ideal.val ≤ v.asIdeal}) ψ)
    (htwist : ∀ J : Ideal (𝓞 F), J ≠ ⊥ →
      J ⊔ (A.modulus * χ.conductor * ψ.conductor) = ⊤ →
      ψ.character J = η J * star (χ.character J)) :
    ∀ p : ExteriorPrime A, (U.j p).val = 0 →
      (p.val.asIdeal ⊔ χ.conductor = ⊤ ∧ p.val.asIdeal ⊔ ψ.conductor = ⊤) ∧
      (chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) =
        χ.character p.val.asIdeal ∧
      η p.val.asIdeal * star (chi (σ := σ) p
        (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u)) =
        ψ.character p.val.asIdeal) := by
  classical
  intro p hj
  have hv : p.val ∉ A.Sf :=
    ArithmeticContext.actual_exterior_prime_outside A (primeIdeal p) p.val rfl
  have he : idealPrimeExponent p.val.asIdeal U.ideal.val = 0 := hj
  have hnot : ¬ U.ideal.val ≤ p.val.asIdeal := by
    intro hle
    have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff U.ideal.property.1).mpr
      ⟨p.val.prime, Ideal.dvd_iff_le.mpr hle⟩
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
    have hs := U.unitPart_spec p
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
  exact ⟨⟨hpc, hpp⟩, hchi, by rw [hchi]; exact htw.symm⟩

end DedekindZetaZeroFree.FrequencyCharacterMasks.KummerConductors

end

end

section

open scoped NumberField Classical
open IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.FrequencyCharacterMasks.KummerConductors
set_option autoImplicit false

open LocalFiniteSums CorrectionFactors

theorem multiplicative_mask_identification {F : Type} [Field F] [NumberField F]
    {A : SArithmeticData F} {σ : F →+* ℂ}
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
    {C : A.GeneralArithmeticContext σ η hS}
    (U : Frequency C) (χ : Detector.PrimitiveFrequencyCharacter F)
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

end DedekindZetaZeroFree.FrequencyCharacterMasks.KummerConductors

end

end

section

open scoped NumberField Classical
open IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.FrequencyCharacterMasks
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open LocalFiniteSums CorrectionFactors

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}

def plusExteriorCoefficient (U : Frequency C) (I : A.Exterior) : ℂ :=
  A.sexticResiduePowerChar σ I 1 (Ideal.Quotient.mk (A.extendIdeal I) U.u)

def minusExteriorCoefficient (U : Frequency C) (I : A.Exterior) : ℂ :=
  η I.val * star (plusExteriorCoefficient U I)

def plusCoefficient (U : Frequency C) (I : Ideal (𝓞 F)) : ℂ :=
  if hI : I ≠ ⊥ ∧ I ⊔ A.cS = ⊤ then
    plusExteriorCoefficient U ⟨I, hI⟩ else 0

def minusCoefficient (U : Frequency C) (I : Ideal (𝓞 F)) : ℂ :=
  η I * star (plusCoefficient U I)

def frequencyMask (U : Frequency C) : Set (HeightOneSpectrum (𝓞 F)) :=
  (A.Sf : Set (HeightOneSpectrum (𝓞 F))) ∪ {v | U.ideal.val ≤ v.asIdeal}

 def valuationIdeal (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ A.Sf) : Ideal A.R where
  carrier := {r | v.valuation F (r : F) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change v.valuation F ((x : F) + (y : F)) < 1
    exact (ValuationClass.map_add_le_max _ _ _).trans_lt (max_lt hx hy)
  smul_mem' := by
    intro x y hy
    change v.valuation F ((x : F) * (y : F)) < 1
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (x.property v hv) zero_le).trans_lt (by simpa using hy)
private lemma support_iff (U : Frequency C) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ A.Sf) : U.ideal.val ≤ v.asIdeal ↔ v.valuation F (U.u : F) < 1 := by
  constructor
  · intro h
    have hm : A.extendIdeal U.ideal ≤ valuationIdeal A v hv := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      change v.valuation F (algebraMap (𝓞 F) F a) < 1
      exact (v.valuation_lt_one_iff_mem (K := F) a).mpr (h ha)
    apply hm
    rw [← U.generates.2]
    exact Ideal.mem_span_singleton_self _
  · intro h a ha
    have ham : algebraMap (𝓞 F) A.R a ∈ Ideal.span ({U.u} : Set A.R) := by
      rw [U.generates.2]
      exact Ideal.mem_map_of_mem _ ha
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp ham
    apply (v.valuation_lt_one_iff_mem (K := F) a).mp
    have he := congrArg (fun r : A.R => (r : F)) hy
    change (a : F) = (U.u : F) * (y : F) at he
    change v.valuation F (a : F) < 1
    rw [he, map_mul]
    exact (mul_le_mul_of_nonneg_left (y.property v hv) zero_le).trans_lt (by simpa using h)

theorem frequencyMask_eq_principal_support (U : Frequency C) :
    frequencyMask U = (A.Sf : Set (HeightOneSpectrum (𝓞 F))) ∪
      Detector.exteriorFrequencyPrimeSupport F
        (A.Sf : Set (HeightOneSpectrum (𝓞 F))) U.u := by
  ext v
  simp only [frequencyMask, Detector.exteriorFrequencyPrimeSupport,
    Set.mem_union, Set.mem_setOf_eq]
  by_cases hv : v ∈ A.Sf
  · simp [hv]
  · simp [hv, support_iff U v hv]

private lemma plus_base (U : Frequency C) (I : A.Exterior) :
    plusExteriorCoefficient U I = σ (A.sexticResidue I U.u) := by
  simp only [plusExteriorCoefficient, SArithmeticData.sexticResiduePowerChar,
    SArithmeticData.sexticExponent, show (1 : ℤ) % 6 = 1 from rfl,
    Int.toNat_one, pow_one]
  by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) U.u)
  · change _ = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [← hx.unit_spec, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
    rfl
  · rw [MulChar.map_nonunit _ hx]
    change 0 = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [MulChar.map_nonunit _ hx, map_zero]
private lemma plus_ext_mul (U : Frequency C) (I J : A.Exterior) :
    plusExteriorCoefficient U (ExteriorIdealEuler.mul I J) =
      plusExteriorCoefficient U I * plusExteriorCoefficient U J := by
  simp only [plus_base]
  rw [show A.sexticResidue (ExteriorIdealEuler.mul I J) U.u =
    A.sexticResidue I U.u * A.sexticResidue J U.u from
      A.sexticResidueFamily_normalized.2.2 I J _ rfl U.u, map_mul]
private lemma plus_ext_one (U : Frequency C) :
    plusExteriorCoefficient U (ExteriorIdealEuler.one A.cS) = 1 := by
  rw [plus_base]
  rw [show A.sexticResidue (ExteriorIdealEuler.one A.cS) U.u = 1 from
    A.residueValue_top _ _ rfl _, map_one]
private lemma plus_ext_norm (U : Frequency C) (I : A.Exterior) :
    ‖plusExteriorCoefficient U I‖ ≤ 1 := by
  rw [plus_base]
  by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) U.u)
  · change ‖σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)‖ ≤ 1
    rw [← hx.unit_spec, MulChar.ofUnitHom_coe]
    have hp := A.sexticResidueFamily_normalized.1 I hx.unit
    have hp' : σ ((A.sexticResidueFamily I hx.unit : Fˣ) : F) ^ 6 = 1 := by
      rw [← map_pow]
      simpa using congrArg (fun u : Fˣ => σ (u : F)) hp
    exact (Complex.norm_eq_one_of_pow_eq_one hp' (by decide)).le
  · change ‖σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)‖ ≤ 1
    rw [MulChar.map_nonunit _ hx, map_zero, norm_zero]
    exact zero_le_one
private lemma plus_ext_pow (U : Frequency C) (I : A.Exterior) (k : ℕ) :
    plusExteriorCoefficient U (ExteriorIdealEuler.pow I k) =
      plusExteriorCoefficient U I ^ k := by
  induction k with
  | zero => simpa [ExteriorIdealEuler.pow, ExteriorIdealEuler.one] using plus_ext_one U
  | succ k ih =>
    have he : ExteriorIdealEuler.pow I (k+1) =
        ExteriorIdealEuler.mul (ExteriorIdealEuler.pow I k) I := by
      apply Subtype.ext; simp [ExteriorIdealEuler.pow, ExteriorIdealEuler.mul, pow_succ]
    rw [he, plus_ext_mul, ih, pow_succ]
private lemma plus_mul (U : Frequency C) (I J : Ideal (𝓞 F)) :
    plusCoefficient U (I * J) = plusCoefficient U I * plusCoefficient U J := by
  have he : (I * J ≠ ⊥ ∧ I * J ⊔ A.cS = ⊤) ↔
      (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) ∧ (J ≠ ⊥ ∧ J ⊔ A.cS = ⊤) := by
    constructor
    · intro h
      have hI : I ⊔ A.cS = ⊤ := top_unique (by
        rw [← h.2]; exact sup_le_sup_right Ideal.mul_le_left _)
      have hJ : J ⊔ A.cS = ⊤ := top_unique (by
        rw [← h.2]; exact sup_le_sup_right Ideal.mul_le_right _)
      exact ⟨⟨left_ne_zero_of_mul h.1, hI⟩, right_ne_zero_of_mul h.1, hJ⟩
    · rintro ⟨hI,hJ⟩
      refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
      rw [Ideal.mul_sup_eq_of_coprime_left hI.2]
      exact hJ.2
  unfold plusCoefficient
  by_cases hI : I ≠ ⊥ ∧ I ⊔ A.cS = ⊤
  · by_cases hJ : J ≠ ⊥ ∧ J ⊔ A.cS = ⊤
    · rw [dif_pos (he.mpr ⟨hI,hJ⟩), dif_pos hI, dif_pos hJ]
      exact plus_ext_mul U ⟨I,hI⟩ ⟨J,hJ⟩
    · rw [dif_neg (fun h => hJ (he.mp h).2), dif_pos hI, dif_neg hJ, mul_zero]
  · rw [dif_neg (fun h => hI (he.mp h).1), dif_neg hI, zero_mul]
private lemma minus_mul (U : Frequency C) (I J : Ideal (𝓞 F)) :
    minusCoefficient U (I * J) = minusCoefficient U I * minusCoefficient U J := by
  simp only [minusCoefficient, RayClassCharacter.map_mul', plus_mul, star_mul]
  ring

theorem actual_coefficients_multiplicative (U : Frequency C) :
    ExteriorIdealEuler.IsCoefficient (plusExteriorCoefficient U) ∧
      ExteriorIdealEuler.IsCoefficient (minusExteriorCoefficient U) ∧
      (∀ I J : Ideal (𝓞 F),
        plusCoefficient U (I * J) = plusCoefficient U I * plusCoefficient U J) ∧
      (∀ I J : Ideal (𝓞 F),
        minusCoefficient U (I * J) = minusCoefficient U I * minusCoefficient U J) := by
  refine ⟨⟨plus_ext_one U, fun I J _ => plus_ext_mul U I J,
    plus_ext_norm U, fun p k => plus_ext_pow U p.val k⟩, ?_, plus_mul U, minus_mul U⟩
  constructor
  · rw [minusExteriorCoefficient, plus_ext_one]
    simp [ExteriorIdealEuler.one, RayClassCharacter.map_top']
  · intro I J h
    rw [minusExteriorCoefficient, plus_ext_mul]
    simp only [minusExteriorCoefficient, ExteriorIdealEuler.mul, RayClassCharacter.map_mul',
      star_mul]
    ring
  · intro I
    rw [minusExteriorCoefficient, norm_mul, norm_star]
    exact mul_le_one₀ (RayUnitary.ray_character_norm_le_one F A.modulus A.modulus_ne_zero η I.val)
      (norm_nonneg _) (plus_ext_norm U I)
  · intro p k
    have hη : η (p.val.val ^ k) = η p.val.val ^ k := by
      induction k with
      | zero => simp [RayClassCharacter.map_top']
      | succ k ih => rw [pow_succ, RayClassCharacter.map_mul', ih, pow_succ]
    rw [minusExteriorCoefficient, plus_ext_pow]
    simp only [minusExteriorCoefficient, ExteriorIdealEuler.pow, hη,
      star_pow, mul_pow]

theorem actual_coefficients_zero_at_frequency_primes
    (U : Frequency C) (p : ExteriorPrime A) (hp : (U.j p).val ≠ 0) :
    chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) = 0 ∧
      η p.val.asIdeal *
        star (chi (σ := σ) p
          (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u)) = 0 ∧
      plusCoefficient U p.val.asIdeal = 0 ∧
      minusCoefficient U p.val.asIdeal = 0 := by
  letI : Nontrivial (A.R ⧸ A.extendIdeal (primeIdeal p)) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (A.residue_extendIdeal_ne_top (primeIdeal p) p.val.isPrime.ne_top)
  have hg : Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (generator C p) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← (generator_generates C p).2]
    exact Ideal.mem_span_singleton_self _
  have hu : Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u = 0 := by
    rw [(U.unitPart_spec p).1, map_mul, map_pow, hg, zero_pow hp, zero_mul]
  have hchi : chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) = 0 := by
    rw [hu, MulChar.map_zero]

  have htwist : η p.val.asIdeal * star (chi (σ := σ) p
          (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u)) = 0 := by
    simp [hchi]
  have hplus : plusCoefficient U p.val.asIdeal = 0 := by
    unfold plusCoefficient
    rw [dif_pos ⟨p.val.ne_bot, p.property⟩]
    exact hchi
  refine ⟨hchi, htwist, hplus, ?_⟩
  simp [minusCoefficient, hplus]

structure PrimitiveInducers (U : Frequency C) where
  plus : Detector.PrimitiveFrequencyCharacter F
  minus : Detector.PrimitiveFrequencyCharacter F
  kummer : Detector.IsKummerFrequencyCharacter F A.zeta12 σ
    (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
    (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) plus
  twist : ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
    I ⊔ (A.modulus * plus.conductor * minus.conductor) = ⊤ →
      minus.character I = η I * star (plus.character I)
  plus_support : Detector.conductorSupportedOn F (frequencyMask U) plus
  minus_support : Detector.conductorSupportedOn F (frequencyMask U) minus
  plus_order : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ plus.conductor = ⊤ →
    plus.character I ^ (6 : ℕ) = 1
  minus_order : ∃ e : ℕ, 0 < e ∧
    ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ minus.conductor = ⊤ →
      minus.character I ^ e = 1
  exterior_unramified : ∀ p : ExteriorPrime A, (U.j p).val = 0 →
    p.val.asIdeal ⊔ plus.conductor = ⊤ ∧ p.val.asIdeal ⊔ minus.conductor = ⊤
  exterior_values : ∀ p : ExteriorPrime A, (U.j p).val = 0 →
    chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) =
      plus.character p.val.asIdeal ∧
    η p.val.asIdeal * star (chi (σ := σ) p
      (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u)) =
      minus.character p.val.asIdeal
  plus_mask : ∀ I : Ideal (𝓞 F), plusCoefficient U I =
    Detector.deletedPrimitiveIdealCoefficient F plus (frequencyMask U) I
  minus_mask : ∀ I : Ideal (𝓞 F), minusCoefficient U I =
    Detector.deletedPrimitiveIdealCoefficient F minus (frequencyMask U) I

theorem primitiveInducers_exists (U : Frequency C) :
    Nonempty (PrimitiveInducers U) := by
  obtain ⟨χ, hχ, hχS, hχorder⟩ :=
    KummerConductors.kummer_inducer_exists A σ U.ideal U.u U.generates
  obtain ⟨ψ, htwist, hψS, hψorder⟩ :=
    KummerConductors.finite_order_twist_inducer_exists A η (frequencyMask U)
      Set.subset_union_left χ hχS 6 (by decide) hχorder
  have hprimes := KummerConductors.exterior_prime_identification U χ ψ hχ hψS htwist
  have hplusone : plusCoefficient U ⊤ = 1 := by
    unfold plusCoefficient
    rw [dif_pos ⟨top_ne_bot, by simp⟩]
    exact plus_ext_one U
  have hminusone : minusCoefficient U ⊤ = 1 := by
    simp [minusCoefficient, hplusone, RayClassCharacter.map_top']
  have hplusoutside : ∀ I : Ideal (𝓞 F),
      ¬ (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) → plusCoefficient U I = 0 := by
    intro I hI
    simp [plusCoefficient, hI]
  have hminusoutside : ∀ I : Ideal (𝓞 F),
      ¬ (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) → minusCoefficient U I = 0 := by
    intro I hI
    simp [minusCoefficient, hplusoutside I hI]
  have hplusprime : ∀ p : ExteriorPrime A, plusCoefficient U p.val.asIdeal =
      if (U.j p).val = 0 then χ.character p.val.asIdeal else 0 := by
    intro p
    by_cases hp : (U.j p).val = 0
    · rw [if_pos hp]
      unfold plusCoefficient
      rw [dif_pos ⟨p.val.ne_bot, p.property⟩]
      exact (hprimes p hp).2.1
    · rw [if_neg hp]
      exact (actual_coefficients_zero_at_frequency_primes U p hp).2.2.1
  have hminusprime : ∀ p : ExteriorPrime A, minusCoefficient U p.val.asIdeal =
      if (U.j p).val = 0 then ψ.character p.val.asIdeal else 0 := by
    intro p
    by_cases hp : (U.j p).val = 0
    · rw [if_pos hp]
      unfold minusCoefficient plusCoefficient
      rw [dif_pos ⟨p.val.ne_bot, p.property⟩]
      exact (hprimes p hp).2.2
    · rw [if_neg hp]
      exact (actual_coefficients_zero_at_frequency_primes U p hp).2.2.2
  exact ⟨{
    plus := χ
    minus := ψ
    kummer := hχ
    twist := htwist
    plus_support := hχS
    minus_support := hψS
    plus_order := hχorder
    minus_order := hψorder
    exterior_unramified := fun p hp => (hprimes p hp).1
    exterior_values := fun p hp => (hprimes p hp).2
    plus_mask := KummerConductors.multiplicative_mask_identification U χ (plusCoefficient U)
      hplusone (plus_mul U) hplusoutside hplusprime
    minus_mask := KummerConductors.multiplicative_mask_identification U ψ (minusCoefficient U)
      hminusone (minus_mul U) hminusoutside hminusprime
  }⟩

def principalCoefficient (A : SArithmeticData F) (I : Ideal (𝓞 F)) : ℂ :=
  if I ≠ ⊥ ∧ I ⊔ A.cS = ⊤ then 1 else 0

private lemma not_div_iff (A : SArithmeticData F) (I : Ideal (𝓞 F)) :
    (¬ ∃ v ∈ (A.Sf : Set (HeightOneSpectrum (𝓞 F))), I ≤ v.asIdeal) ↔ I ⊔ A.cS = ⊤ := by
  constructor
  · intro h
    apply Ideal.sup_prod_eq_top
    intro v hv
    have hn : ¬ I ≤ v.asIdeal := fun hh => h ⟨v, hv, hh⟩
    exact (Ideal.isMaximal_def.mp v.isMaximal).2 _ (lt_of_le_of_ne le_sup_right (by
      intro he
      exact hn ((le_sup_left : I ≤ I ⊔ v.asIdeal).trans_eq he.symm)))
  · intro h ⟨v, hv, hh⟩
    have hc : A.cS ≤ v.asIdeal :=
      (Ideal.prod_le_inf : A.cS ≤ A.Sf.inf (fun w => w.asIdeal)).trans (Finset.inf_le hv)
    have ht : (⊤ : Ideal (𝓞 F)) ≤ v.asIdeal := by rw [← h]; exact sup_le hh hc
    exact v.isPrime.ne_top (top_unique ht)

theorem principal_mask_exactly_S (A : SArithmeticData F) :
    (Detector.FrequencyPrincipal.principalPrimitive (F := F)).conductor = ⊤ ∧
      (∀ I : Ideal (𝓞 F), principalCoefficient A I =
        Detector.deletedPrimitiveIdealCoefficient F
          (Detector.FrequencyPrincipal.principalPrimitive (F := F))
          (A.Sf : Set (HeightOneSpectrum (𝓞 F))) I) ∧
      (∀ I : A.Exterior, principalCoefficient A I.val = 1) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro I
    unfold principalCoefficient Detector.deletedPrimitiveIdealCoefficient
    by_cases h : ∃ v ∈ (A.Sf : Set (HeightOneSpectrum (𝓞 F))), I ≤ v.asIdeal
    · have hc : I ⊔ A.cS ≠ ⊤ := mt (not_div_iff A I).mpr (not_not.mpr h)
      rw [if_neg (fun hh => hc hh.2), if_pos h]
    · have hc := (not_div_iff A I).mp h
      rw [if_neg h]
      simp only [hc, and_true]
      simp [Detector.FrequencyPrincipal.principalPrimitive,
        Detector.FrequencyPrincipal.principalRay]
  · intro I
    simp [principalCoefficient, I.property.1, I.property.2]

end DedekindZetaZeroFree.FrequencyCharacterMasks

end

end
