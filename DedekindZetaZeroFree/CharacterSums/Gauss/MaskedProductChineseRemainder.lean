module

public import DedekindZetaZeroFree.CharacterSums.Gauss.PrimePowerChineseRemainders
public import DedekindZetaZeroFree.CharacterSums.Gauss.LocalUnitRescaling

@[expose] public section

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.MaskedProductAssembly
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

def indexedPrime (A : SArithmeticData F)
    (P : Finset (HeightOneSpectrum (𝓞 F)))
    (p : P → A.Exterior) (hp : ∀ v : P, (p v).val = v.val.asIdeal)
    (v : P) : LocalFiniteSums.ExteriorPrime A :=
  ⟨v.val, by rw [← hp v]; exact (p v).property.2⟩

@[simp] theorem indexedPrime_ideal (A : SArithmeticData F)
    (P : Finset (HeightOneSpectrum (𝓞 F)))
    (p : P → A.Exterior) (hp : ∀ v : P, (p v).val = v.val.asIdeal) (v : P) :
    LocalFiniteSums.primeIdeal (indexedPrime A P p hp v) = p v := by
  exact Subtype.ext (hp v).symm

private theorem span_prod (A : SArithmeticData F) {ι : Type*}
    (T : Finset ι) (f : ι → A.R) :
    Ideal.span {∏ i ∈ T, f i} = ∏ i ∈ T, Ideal.span {f i} := by
  induction T using Finset.induction_on with
  | empty => simp [Ideal.span_singleton_one, Ideal.one_eq_top]
  | @insert i T hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      ← Ideal.span_singleton_mul_span_singleton, ih]

private theorem product_generates (A : SArithmeticData F)
    (I : A.Exterior) (P : Finset (HeightOneSpectrum (𝓞 F)))
    (p : P → A.Exterior) (hp : ∀ v : P, (p v).val = v.val.asIdeal)
    (π : P → A.R) (hπ : ∀ v : P, A.Generates (p v) (π v))
    (e : P → ℕ) (hI : I.val = ∏ v : P, v.val.asIdeal ^ e v) :
    A.Generates I (∏ v : P, π v ^ e v) := by
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ (hπ v).1), ?_⟩
  rw [span_prod]
  change _ = Ideal.map (algebraMap (𝓞 F) A.R) I.val
  conv_rhs => rw [hI]
  rw [show Ideal.map (algebraMap (𝓞 F) A.R) =
    Ideal.mapHom (algebraMap (𝓞 F) A.R) from rfl, map_prod]
  apply Finset.prod_congr rfl
  intro v _
  rw [← Ideal.span_singleton_pow, (hπ v).2]
  change Ideal.map (algebraMap (𝓞 F) A.R) (p v).val ^ _ = _
  rw [hp v]
  exact (Ideal.map_pow (algebraMap (𝓞 F) A.R) v.val.asIdeal _).symm

private theorem exponent_mul (q I K : Ideal (𝓞 F)) (hI : I ≠ 0) (hK : K ≠ 0) :
    idealPrimeExponent q (I * K) = idealPrimeExponent q I + idealPrimeExponent q K := by
  simp [idealPrimeExponent, UniqueFactorizationMonoid.normalizedFactors_mul hI hK]

private theorem exponent_pow (q I : Ideal (𝓞 F)) (n : ℕ) :
    idealPrimeExponent q (I ^ n) = n * idealPrimeExponent q I := by
  simp [idealPrimeExponent, UniqueFactorizationMonoid.normalizedFactors_pow]

private theorem exponent_prod {ι : Type*} (T : Finset ι)
    (f : ι → Ideal (𝓞 F)) (hf : ∀ i ∈ T, f i ≠ 0) (q : Ideal (𝓞 F)) :
    idealPrimeExponent q (∏ i ∈ T, f i) = ∑ i ∈ T, idealPrimeExponent q (f i) := by
  induction T using Finset.induction_on with
  | empty => simp [idealPrimeExponent, ← Ideal.one_eq_top]
  | @insert i T hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      exponent_mul q _ _ (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

private theorem exponent_prime (q v : HeightOneSpectrum (𝓞 F)) :
    idealPrimeExponent q.asIdeal v.asIdeal = if q = v then 1 else 0 := by
  simp only [idealPrimeExponent,
    UniqueFactorizationMonoid.normalizedFactors_irreducible v.irreducible,
    normalize_eq, Multiset.count_singleton]
  congr 1
  exact propext HeightOneSpectrum.ext_iff.symm

private theorem exponent_prime_product (P : Finset (HeightOneSpectrum (𝓞 F)))
    (e : P → ℕ) (q : HeightOneSpectrum (𝓞 F)) :
    idealPrimeExponent q.asIdeal (∏ v : P, v.val.asIdeal ^ e v) =
      ∑ v : P, if q = v.val then e v else 0 := by
  rw [exponent_prod _ _ (fun v _ => pow_ne_zero _ v.val.ne_bot)]
  apply Finset.sum_congr rfl
  intro v _
  rw [exponent_pow, exponent_prime]
  split <;> simp_all

private theorem exponent_off_support (P : Finset (HeightOneSpectrum (𝓞 F)))
    (e : P → ℕ) (q : HeightOneSpectrum (𝓞 F))
    (hq : ¬ ∃ v : P, q = v.val) :
    idealPrimeExponent q.asIdeal (∏ v : P, v.val.asIdeal ^ e v) = 0 := by
  rw [exponent_prime_product]
  apply Finset.sum_eq_zero
  intro v _
  exact if_neg (fun h => hq ⟨v, h⟩)

theorem prime_product_assembly_data
    (A : SArithmeticData F)
    (Ic In Is Ir Iu : A.Exterior) (u : A.R) (hu : A.Generates Iu u)
    (P : Finset (HeightOneSpectrum (𝓞 F)))
    (p : P → A.Exterior) (hp : ∀ v : P, (p v).val = v.val.asIdeal)
    (π : P → A.R) (hπ : ∀ v : P, A.Generates (p v) (π v))
    (hSupport : ∀ I ∈ ({Ic, In, Is, Ir, Iu} : Finset A.Exterior),
      I.val = ∏ v : P, v.val.asIdeal ^ idealPrimeExponent v.val.asIdeal I.val)
    (n m : ℕ) :
    let k := fun v : P => idealPrimeExponent v.val.asIdeal Is.val
    let t := fun v : P => idealPrimeExponent v.val.asIdeal Ic.val +
      n * idealPrimeExponent v.val.asIdeal In.val
    let J := fun v : P => idealPrimeExponent v.val.asIdeal Iu.val +
      m * idealPrimeExponent v.val.asIdeal Ir.val
    ∃ Ia Ih : A.Exterior,
      ∃ hs : A.Generates Is (∏ v : P, π v ^ k v),
      ∃ ha : A.Generates Ia (∏ v : P, π v ^ t v),
      ∃ hh : A.Generates Ih
        (u * (∏ v : P, π v ^ idealPrimeExponent v.val.asIdeal Ir.val) ^ m),
      (∀ v : P,
        MaskedQuotientCRT.primeExponent (indexedPrime A P p hp v) Is = k v ∧
        MaskedQuotientCRT.primeExponent (indexedPrime A P p hp v) Ia = t v ∧
        MaskedQuotientCRT.primeExponent (indexedPrime A P p hp v) Ih = J v) ∧
      (∀ q : LocalFiniteSums.ExteriorPrime A,
        (MaskedQuotientCRT.primeExponent q Is ≠ 0 ∨
         MaskedQuotientCRT.primeExponent q Ia ≠ 0 ∨
         MaskedQuotientCRT.primeExponent q Ih ≠ 0) →
        ∃ v : P, q.val = v.val) := by
  classical
  dsimp only
  let Ia : A.Exterior := ⟨Ic.val * In.val ^ n,
    mul_ne_zero Ic.property.1 (pow_ne_zero _ In.property.1),
    by rw [Ideal.mul_sup_eq_of_coprime_left Ic.property.2];
       exact Ideal.pow_sup_eq_top In.property.2⟩
  let Ih : A.Exterior := ⟨Iu.val * Ir.val ^ m,
    mul_ne_zero Iu.property.1 (pow_ne_zero _ Ir.property.1),
    by rw [Ideal.mul_sup_eq_of_coprime_left Iu.property.2];
       exact Ideal.pow_sup_eq_top Ir.property.2⟩
  have hsupp (I : A.Exterior) (hI : I ∈ ({Ic, In, Is, Ir, Iu} : Finset A.Exterior)) :=
    hSupport I hI
  have hIs := hsupp Is (by simp)
  have hIc := hsupp Ic (by simp)
  have hIn := hsupp In (by simp)
  have hIr := hsupp Ir (by simp)
  have hIu := hsupp Iu (by simp)
  have hIa : Ia.val = ∏ v : P, v.val.asIdeal ^
      (idealPrimeExponent v.val.asIdeal Ic.val + n * idealPrimeExponent v.val.asIdeal In.val) := by
    change Ic.val * In.val ^ n = _
    conv_lhs => rw [hIc, hIn]
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v _
    rw [pow_add, Nat.mul_comm n, pow_mul]
  have hs := product_generates A Is P p hp π hπ _ hIs
  have ha := product_generates A Ia P p hp π hπ _ hIa
  have hr := product_generates A Ir P p hp π hπ _ hIr
  have hh : A.Generates Ih
      (u * (∏ v : P, π v ^ idealPrimeExponent v.val.asIdeal Ir.val) ^ m) := by
    refine ⟨mul_ne_zero hu.1 (pow_ne_zero _ hr.1), ?_⟩
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hu.2, hr.2]
    change Ideal.map (algebraMap (𝓞 F) A.R) Iu.val *
      Ideal.map (algebraMap (𝓞 F) A.R) Ir.val ^ m =
      Ideal.map (algebraMap (𝓞 F) A.R) (Iu.val * Ir.val ^ m)
    rw [Ideal.map_mul, Ideal.map_pow]
  refine ⟨Ia, Ih, hs, ha, hh, ?_, ?_⟩
  · intro v
    change idealPrimeExponent v.val.asIdeal Is.val = _ ∧
      idealPrimeExponent v.val.asIdeal (Ic.val * In.val ^ n) = _ ∧
      idealPrimeExponent v.val.asIdeal (Iu.val * Ir.val ^ m) = _
    rw [exponent_mul _ _ _ Ic.property.1 (pow_ne_zero _ In.property.1),
      exponent_mul _ _ _ Iu.property.1 (pow_ne_zero _ Ir.property.1),
      exponent_pow, exponent_pow]
    exact ⟨rfl, rfl, rfl⟩
  · intro q hq
    by_contra hnot
    have hz (I : A.Exterior) (hI : I ∈ ({Ic, In, Is, Ir, Iu} : Finset A.Exterior)) :
        idealPrimeExponent q.val.asIdeal I.val = 0 := by
      rw [hsupp I hI]
      exact exponent_off_support P _ q.val hnot
    have hzIs := hz Is (by simp)
    have hzIc := hz Ic (by simp)
    have hzIn := hz In (by simp)
    have hzIr := hz Ir (by simp)
    have hzIu := hz Iu (by simp)
    change (idealPrimeExponent q.val.asIdeal Is.val ≠ 0 ∨
      idealPrimeExponent q.val.asIdeal (Ic.val * In.val ^ n) ≠ 0 ∨
      idealPrimeExponent q.val.asIdeal (Iu.val * Ir.val ^ m) ≠ 0) at hq
    rw [exponent_mul _ _ _ Ic.property.1 (pow_ne_zero _ In.property.1),
      exponent_mul _ _ _ Iu.property.1 (pow_ne_zero _ Ir.property.1),
      exponent_pow, exponent_pow, hzIs, hzIc, hzIn, hzIr, hzIu] at hq
    simpa using hq

end
end DedekindZetaZeroFree.MaskedProductAssembly

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.MaskedProductAssembly
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

theorem indexed_coefficient_crt
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (D : ComparisonPoissonCoefficientData F A)
    (hCharacter : ∀ (I : A.Exterior) (a : A.R) (ha : A.Generates I a),
      D.character a = GeneratorInvariance.transportCharacter _ _ ha.2.symm
        (A.sexticResiduePowerChar σ I 1))
    (hTrace : ∀ x : F, D.additiveCharacter x = (A.fieldTraceCharacter x : ℂ))
    (Is Ia Ih : A.Exterior) (s a h : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a) (hh : A.Generates Ih h)
    (hsAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (s : F) (by exact_mod_cast hs.1)))
    (haAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : F) (by exact_mod_cast ha.1)))
    (P : Finset (HeightOneSpectrum (𝓞 F)))
    (p : P → A.Exterior) (hp : ∀ v : P, (p v).val = v.val.asIdeal)
    (hSupport : ∀ q : LocalFiniteSums.ExteriorPrime A,
      (MaskedQuotientCRT.primeExponent q Is ≠ 0 ∨
       MaskedQuotientCRT.primeExponent q Ia ≠ 0 ∨
       MaskedQuotientCRT.primeExponent q Ih ≠ 0) →
      ∃ v : P, q.val = v.val) :
    GeneratorInvariance.coefficient A D s a h hs.1 ha.1 =
      ∏ v : P, CompatiblePrimeRawLocal.R C (indexedPrime A P p hp v)
        (MaskedQuotientCRT.primeExponent (indexedPrime A P p hp v) Ia)
        (MaskedQuotientCRT.primeExponent (indexedPrime A P p hp v) Is)
        (MaskedQuotientCRT.primeExponent (indexedPrime A P p hp v) Ih)
        (MaskedQuotientCRT.localUnitPart C (indexedPrime A P p hp v) Is s hs)
        (MaskedQuotientCRT.localUnitPart C (indexedPrime A P p hp v) Ia a ha)
        (MaskedQuotientCRT.localUnitPart C (indexedPrime A P p hp v) Ih h hh) := by
  let Q : Finset (LocalFiniteSums.ExteriorPrime A) :=
    (Finset.univ : Finset P).image (indexedPrime A P p hp)
  have hinj : Set.InjOn (indexedPrime A P p hp) ↑(Finset.univ : Finset P) := by
    intro x _ y _ hxy
    exact Subtype.ext (by
      simpa only [indexedPrime] using
        congrArg (fun z : LocalFiniteSums.ExteriorPrime A => z.val) hxy)
  have hmemS : ∀ q : LocalFiniteSums.ExteriorPrime A,
      MaskedQuotientCRT.primeExponent q Is ≠ 0 → q ∈ Q := by
    intro q hq
    obtain ⟨v, hv⟩ := hSupport q (Or.inl hq)
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, Subtype.ext hv.symm⟩
  have hmemA : ∀ q : LocalFiniteSums.ExteriorPrime A,
      MaskedQuotientCRT.primeExponent q Ia ≠ 0 → q ∈ Q := by
    intro q hq
    obtain ⟨v, hv⟩ := hSupport q (Or.inr (Or.inl hq))
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, Subtype.ext hv.symm⟩
  have hmemH : ∀ q : LocalFiniteSums.ExteriorPrime A,
      MaskedQuotientCRT.primeExponent q Ih ≠ 0 → q ∈ Q := by
    intro q hq
    obtain ⟨v, hv⟩ := hSupport q (Or.inr (Or.inr hq))
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, Subtype.ext hv.symm⟩
  have hcoeff : GeneratorInvariance.coefficient A D s a h hs.1 ha.1 =
      MaskedQuotientCRT.coefficient C Is Ia s a h hs ha := by
    unfold GeneratorInvariance.coefficient MaskedQuotientCRT.coefficient
    rw [hCharacter Is s hs, hCharacter Ia a ha]
    have he : D.additiveCharacter =
        Circle.coeHom.compAddChar A.fieldTraceCharacter := by
      ext x
      exact hTrace x
    rw [he]
    congr 1 <;> exact Subsingleton.elim _ _
  rw [hcoeff]
  rw [MaskedQuotientCRT.full_prime_power_crt C Is Ia Ih s a h hs ha hh
    hsAllowed haAllowed Q hmemS hmemA hmemH]
  rw [Finset.prod_image hinj]

end
end DedekindZetaZeroFree.MaskedProductAssembly

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.MaskedProductAssembly
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

private theorem transport
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (p : LocalFiniteSums.ExteriorPrime A)
    (π : A.R) (hπ : A.Generates (LocalFiniteSums.primeIdeal p) π)
    (I : A.Exterior) (x x₀ : A.R) (hx : A.Generates I x)
    (hfree : x = π ^ MaskedQuotientCRT.primeExponent p I * x₀)
    (u₀ : (LocalFiniteSums.LocalIntegers p)ˣ)
    (hu₀ : (u₀.val : LocalFiniteSums.LocalField p) =
      algebraMap F (LocalFiniteSums.LocalField p) (x₀ : F)) :
    MaskedQuotientCRT.localUnitPart C p I x hx =
      MaskedQuotientCRT.localUnitPart C p (LocalFiniteSums.primeIdeal p) π hπ ^
        MaskedQuotientCRT.primeExponent p I * u₀ := by
  have hp : MaskedQuotientCRT.primeExponent p (LocalFiniteSums.primeIdeal p) = 1 := by
    simp [MaskedQuotientCRT.primeExponent, LocalFiniteSums.primeIdeal,
      idealPrimeExponent,
      UniqueFactorizationMonoid.normalizedFactors_irreducible p.val.irreducible]
  apply Units.ext
  apply Subtype.ext
  change ((MaskedQuotientCRT.localUnitPart C p I x hx).val :
      LocalFiniteSums.LocalField p) = _
  rw [MaskedQuotientCRT.localUnitPart_spec]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  change _ = (((MaskedQuotientCRT.localUnitPart C p
    (LocalFiniteSums.primeIdeal p) π hπ).val : LocalFiniteSums.LocalField p) ^
      MaskedQuotientCRT.primeExponent p I) * (u₀.val : LocalFiniteSums.LocalField p)
  rw [MaskedQuotientCRT.localUnitPart_spec, hp, pow_one, hu₀, hfree]
  change algebraMap F (LocalFiniteSums.LocalField p)
      ((π : F) ^ MaskedQuotientCRT.primeExponent p I * (x₀ : F)) / _ = _
  simp only [map_mul, map_pow, div_pow]
  ring

variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem unit_exists
    (p : LocalFiniteSums.ExteriorPrime A) (x : A.R)
    (hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal (LocalFiniteSums.primeIdeal p)) x)) :
    ∃ u : (LocalFiniteSums.LocalIntegers p)ˣ,
      (u.val : LocalFiniteSums.LocalField p) =
        algebraMap F (LocalFiniteSums.LocalField p) (x : F) := by
  let i : LocalFiniteSums.LocalIntegers p :=
    ⟨algebraMap F (LocalFiniteSums.LocalField p) (x : F),
      CompatiblePrimeRawLocal.sInteger_local_integral p x⟩
  let e := A.exteriorLocalResidueEquiv (LocalFiniteSums.primeIdeal p) p.val rfl
  have he := A.exteriorLocalResidueEquiv_apply (LocalFiniteSums.primeIdeal p) p.val rfl x
  have hi_eq : i = A.exteriorIntegerMap (LocalFiniteSums.primeIdeal p) p.val rfl x := rfl
  have hr : IsUnit (IsLocalRing.residue (LocalFiniteSums.LocalIntegers p) i) := by
    rw [hi_eq, ← he]
    exact hx.map e.toRingHom
  have hi : IsUnit i := (IsLocalRing.residue_ne_zero_iff_isUnit i).mp hr.ne_zero
  refine ⟨hi.unit, ?_⟩
  rw [hi.unit_spec]

private theorem chi_embedded
    (p : LocalFiniteSums.ExteriorPrime A) (x : A.R)
    (u : (LocalFiniteSums.LocalIntegers p)ˣ)
    (hu : (u.val : LocalFiniteSums.LocalField p) =
      algebraMap F (LocalFiniteSums.LocalField p) (x : F)) :
    CompatiblePrimeRawLocal.chiOnUnits (σ := σ) p u =
      σ (A.sexticResidue (LocalFiniteSums.primeIdeal p) x) := by
  have he : u.val = ⟨algebraMap F (LocalFiniteSums.LocalField p) (x : F),
      CompatiblePrimeRawLocal.sInteger_local_integral p x⟩ := Subtype.ext hu
  unfold CompatiblePrimeRawLocal.chiOnUnits
  rw [he, CompatiblePrimeRawLocal.localReduction_sInteger]
  change A.sexticResiduePowerChar σ (LocalFiniteSums.primeIdeal p) 1
    (Ideal.Quotient.mk (A.extendIdeal (LocalFiniteSums.primeIdeal p)) x) = _
  unfold SArithmeticData.sexticResiduePowerChar
  rw [show SArithmeticData.sexticExponent 1 = 1 by decide, pow_one]
  unfold SArithmeticData.sexticResidue SArithmeticData.residueValue
  have hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal (LocalFiniteSums.primeIdeal p)) x) := by
    rw [← CompatiblePrimeRawLocal.localReduction_sInteger p x, ← he]
    exact u.isUnit.map (CompatiblePrimeRawLocal.localReduction p)
  rw [← hx.unit_spec, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
  rfl

private theorem cross_unit
    (A : SArithmeticData F)
    (P : Finset (HeightOneSpectrum (𝓞 F)))
    (p : P → A.Exterior) (hp : ∀ v : P, (p v).val = v.val.asIdeal)
    (π : P → A.R) (hπ : ∀ v : P, A.Generates (p v) (π v))
    (v w : P) (hwv : w ≠ v) :
    IsUnit (Ideal.Quotient.mk (A.extendIdeal (p v)) (π w)) := by

  have hne : v.val ≠ w.val := fun h => hwv (Subtype.ext h).symm
  have hcop : IsCoprime (v.val.asIdeal) (w.val.asIdeal) :=
    HeightOneSpectrum.isCoprime_of_ne v.val w.val hne
  have hsup : (p v).val ⊔ (p w).val = ⊤ := by
    rw [hp v, hp w]
    exact hcop.sup_eq

  have hcopR : A.extendIdeal (p v) ⊔ A.extendIdeal (p w) = ⊤ := by
    rw [SArithmeticData.extendIdeal, SArithmeticData.extendIdeal, ← Ideal.map_sup, hsup,
      Ideal.map_top]
  obtain ⟨i, hi, j, hj, hij⟩ := (Ideal.isCoprime_iff_sup_eq.mpr hcopR).exists

  rw [← (hπ w).2] at hj
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hj

  have hunit : IsUnit (Ideal.Quotient.mk (A.extendIdeal (p v)) (π w)) := by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk (A.extendIdeal (p v)) y) ?_
    rw [← map_mul, ← hy]
    have hj_eq : j = 1 - i := by rw [eq_sub_iff_add_eq, add_comm]; exact hij
    rw [hj_eq, map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr hi, sub_zero]
  exact hunit

private theorem chi_mul (p : LocalFiniteSums.ExteriorPrime A)
    (u v : (LocalFiniteSums.LocalIntegers p)ˣ) :
    CompatiblePrimeRawLocal.chiOnUnits (σ := σ) p (u * v) =
      CompatiblePrimeRawLocal.chiOnUnits (σ := σ) p u *
        CompatiblePrimeRawLocal.chiOnUnits (σ := σ) p v := by
  simp only [CompatiblePrimeRawLocal.chiOnUnits, Units.val_mul, map_mul]

private theorem chi_pow (p : LocalFiniteSums.ExteriorPrime A)
    (u : (LocalFiniteSums.LocalIntegers p)ˣ) (n : ℕ) :
    CompatiblePrimeRawLocal.chiOnUnits (σ := σ) p (u ^ n) =
      CompatiblePrimeRawLocal.chiOnUnits (σ := σ) p u ^ n := by
  simp only [CompatiblePrimeRawLocal.chiOnUnits, Units.val_pow_eq_pow_val, map_pow]

private theorem chi_prod {ι : Type*} (p : LocalFiniteSums.ExteriorPrime A)
    (T : Finset ι) (f : ι → (LocalFiniteSums.LocalIntegers p)ˣ) :
    CompatiblePrimeRawLocal.chiOnUnits (σ := σ) p (∏ w ∈ T, f w) =
      ∏ w ∈ T, CompatiblePrimeRawLocal.chiOnUnits (σ := σ) p (f w) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [CompatiblePrimeRawLocal.chiOnUnits]
  | @insert i T hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, chi_mul, ih]

theorem prime_product_local_rescale
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (P : Finset (HeightOneSpectrum (𝓞 F)))
    (p : P → A.Exterior) (hp : ∀ v : P, (p v).val = v.val.asIdeal)
    (π : P → A.R) (hπ : ∀ v : P, A.Generates (p v) (π v))
    (t k j l : P → ℕ) (u : A.R)
    (Is Ia Ih : A.Exterior)
    (hs : A.Generates Is (∏ v : P, π v ^ k v))
    (ha : A.Generates Ia (∏ v : P, π v ^ t v))
    (hh : A.Generates Ih (u * (∏ v : P, π v ^ l v) ^ 6))
    (hdepth : ∀ v : P,
      MaskedQuotientCRT.primeExponent (indexedPrime A P p hp v) Is = k v ∧
      MaskedQuotientCRT.primeExponent (indexedPrime A P p hp v) Ia = t v ∧
      MaskedQuotientCRT.primeExponent (indexedPrime A P p hp v) Ih = j v + 6 * l v)
    (uPrimeFree : P → A.R)
    (hPrimeFree : ∀ v : P, u = π v ^ j v * uPrimeFree v)
    (hPrimeUnit : ∀ v : P,
      IsUnit (Ideal.Quotient.mk (A.extendIdeal (p v)) (uPrimeFree v)))
    (v : P) :
    CompatiblePrimeRawLocal.R C (indexedPrime A P p hp v)
        (t v) (k v) (j v + 6 * l v)
        (MaskedQuotientCRT.localUnitPart C (indexedPrime A P p hp v) Is
          (∏ w : P, π w ^ k w) hs)
        (MaskedQuotientCRT.localUnitPart C (indexedPrime A P p hp v) Ia
          (∏ w : P, π w ^ t w) ha)
        (MaskedQuotientCRT.localUnitPart C (indexedPrime A P p hp v) Ih
          (u * (∏ w : P, π w ^ l w) ^ 6) hh) =
      σ (A.sexticResidue (p v) (uPrimeFree v)) ^ ((k v : ℤ) - (t v : ℤ)) *
        (∏ w ∈ ({v}ᶜ : Finset P), σ (A.sexticResidue (p v) (π w)) ^ k w) ^ (t v : ℤ) *
        (∏ w ∈ ({v}ᶜ : Finset P), σ (A.sexticResidue (p v) (π w)) ^ t w) ^
          ((t v : ℤ) - k v) *
        (let b := MaskedQuotientCRT.localUnitPart C (indexedPrime A P p hp v)
          (LocalFiniteSums.primeIdeal (indexedPrime A P p hp v)) (π v)
          (by simpa using hπ v)
        CompatiblePrimeRawLocal.R C (indexedPrime A P p hp v)
          (t v) (k v) (j v + 6 * l v) (b ^ k v) (b ^ t v) (b ^ (j v + 6 * l v))) := by
  classical
  let q := indexedPrime A P p hp v
  have hq : LocalFiniteSums.primeIdeal q = p v := indexedPrime_ideal A P p hp v
  have hπq : A.Generates (LocalFiniteSums.primeIdeal q) (π v) := by simpa [hq] using hπ v
  let b := MaskedQuotientCRT.localUnitPart C q (LocalFiniteSums.primeIdeal q) (π v) hπq
  have hcross (w : P) (hw : w ≠ v) :
      ∃ z : (LocalFiniteSums.LocalIntegers q)ˣ,
        (z.val : LocalFiniteSums.LocalField q) =
          algebraMap F (LocalFiniteSums.LocalField q) (π w : F) :=
    unit_exists q (π w) (by rw [hq]; exact cross_unit A P p hp π hπ v w hw)
  let U : P → (LocalFiniteSums.LocalIntegers q)ˣ :=
    fun w => if hw : w = v then 1 else (hcross w hw).choose
  have hU (w : P) (hw : w ≠ v) :
      ((U w).val : LocalFiniteSums.LocalField q) =
        algebraMap F (LocalFiniteSums.LocalField q) (π w : F) := by
    simp only [U, dif_neg hw]
    exact (hcross w hw).choose_spec
  let E (e : P → ℕ) : (LocalFiniteSums.LocalIntegers q)ˣ :=
    ∏ w ∈ ({v}ᶜ : Finset P), U w ^ e w
  have hE (e : P → ℕ) :
      ((E e).val : LocalFiniteSums.LocalField q) =
        algebraMap F (LocalFiniteSums.LocalField q)
          ((∏ w ∈ ({v}ᶜ : Finset P), π w ^ e w : A.R) : F) := by
    simp only [E, Units.coe_prod, Units.val_pow_eq_pow_val, SubmonoidClass.coe_finsetProd,
      SubmonoidClass.coe_pow, map_prod, map_pow]
    apply Finset.prod_congr rfl
    intro w hw
    have hwv : w ≠ v := by simpa using hw
    rw [hU w hwv]
  have hχE (e : P → ℕ) :
      CompatiblePrimeRawLocal.chiOnUnits (σ := σ) q (E e) =
        ∏ w ∈ ({v}ᶜ : Finset P), σ (A.sexticResidue (p v) (π w)) ^ e w := by
    dsimp only [E]
    rw [chi_prod]
    apply Finset.prod_congr rfl
    intro w hw
    have hwv : w ≠ v := by simpa using hw
    rw [chi_pow, chi_embedded q (π w) (U w) (hU w hwv), hq]
  obtain ⟨Uu, hUu⟩ := unit_exists q (uPrimeFree v) (by rw [hq]; exact hPrimeUnit v)
  have hsrel : MaskedQuotientCRT.localUnitPart C q Is (∏ w : P, π w ^ k w) hs =
      b ^ k v * E k := by
    have he := transport A σ η hS C q (π v) hπq Is
      (∏ w : P, π w ^ k w) (∏ w ∈ ({v}ᶜ : Finset P), π w ^ k w) hs
      (by rw [(hdepth v).1]; exact Fintype.prod_eq_mul_prod_compl v _) (E k) (hE k)
    simpa only [q, (hdepth v).1] using he
  have harel : MaskedQuotientCRT.localUnitPart C q Ia (∏ w : P, π w ^ t w) ha =
      b ^ t v * E t := by
    have he := transport A σ η hS C q (π v) hπq Ia
      (∏ w : P, π w ^ t w) (∏ w ∈ ({v}ᶜ : Finset P), π w ^ t w) ha
      (by rw [(hdepth v).2.1]; exact Fintype.prod_eq_mul_prod_compl v _) (E t) (hE t)
    simpa only [q, (hdepth v).2.1] using he
  have hhrel : MaskedQuotientCRT.localUnitPart C q Ih
      (u * (∏ w : P, π w ^ l w) ^ 6) hh =
      b ^ (j v + 6 * l v) * (Uu * E l ^ 6) := by
    have he := transport A σ η hS C q (π v) hπq Ih
      (u * (∏ w : P, π w ^ l w) ^ 6)
      (uPrimeFree v * (∏ w ∈ ({v}ᶜ : Finset P), π w ^ l w) ^ 6) hh
      (by
        rw [(hdepth v).2.2, hPrimeFree v, Fintype.prod_eq_mul_prod_compl v,
          mul_pow, pow_add, pow_mul]
        ring)
      (Uu * E l ^ 6) (by
        simp only [Units.val_mul, Units.val_pow_eq_pow_val]
        change (Uu.val : LocalFiniteSums.LocalField q) *
          ((E l).val : LocalFiniteSums.LocalField q) ^ 6 = _
        rw [hUu, hE]
        change _ = algebraMap F (LocalFiniteSums.LocalField q)
          ((uPrimeFree v : F) * ((∏ w ∈ ({v}ᶜ : Finset P), π w ^ l w : A.R) : F) ^ 6)
        rw [map_mul, map_pow])
    simpa only [q, (hdepth v).2.2] using he
  change CompatiblePrimeRawLocal.R C q (t v) (k v) (j v + 6 * l v) _ _ _ = _
  rw [hsrel, harel, hhrel, CompatiblePrimeRawLocal.R_unit_rescale]
  have hχh : CompatiblePrimeRawLocal.chiOnUnits (σ := σ) q (Uu * E l ^ 6) =
      σ (A.sexticResidue (p v) (uPrimeFree v)) := by
    rw [chi_mul, chi_pow, CompatiblePrimeRawLocal.chiOnUnits_pow_six, mul_one,
      chi_embedded q (uPrimeFree v) Uu hUu, hq]
  rw [chi_mul q (b ^ (j v + 6 * l v)) (Uu * E l ^ 6), hχh,
    chi_mul q (b ^ k v) (E k), hχE,
    chi_mul q (b ^ t v) (E t), hχE]
  change _ = σ (A.sexticResidue (p v) (uPrimeFree v)) ^ ((k v : ℤ) - t v) *
    (∏ w ∈ ({v}ᶜ : Finset P), σ (A.sexticResidue (p v) (π w)) ^ k w) ^ (t v : ℤ) *
    (∏ w ∈ ({v}ᶜ : Finset P), σ (A.sexticResidue (p v) (π w)) ^ t w) ^ ((t v : ℤ) - k v) *
    CompatiblePrimeRawLocal.R C q (t v) (k v) (j v + 6 * l v) (b ^ k v) (b ^ t v) (b ^ (j v + 6 * l v))
  rw [CompatiblePrimeRawLocal.R_unit_rescale]
  simp only [mul_zpow]
  ring

end
end DedekindZetaZeroFree.MaskedProductAssembly

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.MaskedProductAssembly
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

theorem cross_prime_residue_ne_zero
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (P : Finset (HeightOneSpectrum (𝓞 F)))
    (p : P → A.Exterior) (hp : ∀ v : P, (p v).val = v.val.asIdeal)
    (π : P → A.R) (hπ : ∀ v : P, A.Generates (p v) (π v))
    (v w : P) (hwv : w ≠ v) :
    σ (A.sexticResidue (p v) (π w)) ≠ 0 := by

  have hne : v.val ≠ w.val := fun h => hwv (Subtype.ext h).symm
  have hcop : IsCoprime (v.val.asIdeal) (w.val.asIdeal) :=
    HeightOneSpectrum.isCoprime_of_ne v.val w.val hne
  have hsup : (p v).val ⊔ (p w).val = ⊤ := by
    rw [hp v, hp w]
    exact hcop.sup_eq

  have hcopR : A.extendIdeal (p v) ⊔ A.extendIdeal (p w) = ⊤ := by
    rw [SArithmeticData.extendIdeal, SArithmeticData.extendIdeal, ← Ideal.map_sup, hsup,
      Ideal.map_top]
  obtain ⟨i, hi, j, hj, hij⟩ := (Ideal.isCoprime_iff_sup_eq.mpr hcopR).exists

  rw [← (hπ w).2] at hj
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hj

  have hunit : IsUnit (Ideal.Quotient.mk (A.extendIdeal (p v)) (π w)) := by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk (A.extendIdeal (p v)) y) ?_
    rw [← map_mul, ← hy]
    have hj_eq : j = 1 - i := by rw [eq_sub_iff_add_eq, add_comm]; exact hij
    rw [hj_eq, map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr hi, sub_zero]

  have hne0 : A.sexticResidue (p v) (π w) ≠ 0 := by
    rw [SArithmeticData.sexticResidue, SArithmeticData.residueValue, ← hunit.unit_spec,
      MulChar.ofUnitHom_coe]
    exact Units.ne_zero _
  exact fun h => hne0 (σ.injective (by rw [h, map_zero]))

end
end DedekindZetaZeroFree.MaskedProductAssembly

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.GaussProductCancellation
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

 theorem coefficient_eq_masked_crt

    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (D : ComparisonPoissonCoefficientData F A)
    (hCharacter : ∀ (I : A.Exterior) (a : A.R) (ha : A.Generates I a),
      D.character a = GeneratorInvariance.transportCharacter _ _ ha.2.symm
        (A.sexticResiduePowerChar σ I 1))
    (hTrace : ∀ x : F, D.additiveCharacter x = (A.fieldTraceCharacter x : ℂ))
    (C : A.GeneralArithmeticContext σ η hS)
    (Is Ia : A.Exterior) (s a h : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a) :
    GeneratorInvariance.coefficient A D s a h hs.1 ha.1 =
      MaskedQuotientCRT.coefficient C Is Ia s a h hs ha := by
  unfold GeneratorInvariance.coefficient MaskedQuotientCRT.coefficient
  rw [hCharacter Is s hs, hCharacter Ia a ha]
  have he : D.additiveCharacter = Circle.coeHom.compAddChar A.fieldTraceCharacter := by
    ext x
    exact hTrace x
  rw [he]
  congr 1 <;> exact Subsingleton.elim _ _

theorem localUnitPart_primeFree_transport
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (p : LocalFiniteSums.ExteriorPrime A)
    (π : A.R) (hπ : A.Generates (LocalFiniteSums.primeIdeal p) π)
    (I : A.Exterior) (x x₀ : A.R) (hx : A.Generates I x)
    (hfree : x = π ^ MaskedQuotientCRT.primeExponent p I * x₀)
    (u₀ : (LocalFiniteSums.LocalIntegers p)ˣ)
    (hu₀ : (u₀.val : LocalFiniteSums.LocalField p) =
      algebraMap F (LocalFiniteSums.LocalField p) (x₀ : F)) :
    MaskedQuotientCRT.localUnitPart C p I x hx =
      MaskedQuotientCRT.localUnitPart C p (LocalFiniteSums.primeIdeal p) π hπ ^
        MaskedQuotientCRT.primeExponent p I * u₀ := by
  have hp : MaskedQuotientCRT.primeExponent p (LocalFiniteSums.primeIdeal p) = 1 := by
    simp [MaskedQuotientCRT.primeExponent, LocalFiniteSums.primeIdeal,
      idealPrimeExponent,
      UniqueFactorizationMonoid.normalizedFactors_irreducible p.val.irreducible]
  apply Units.ext
  apply Subtype.ext
  change ((MaskedQuotientCRT.localUnitPart C p I x hx).val :
      LocalFiniteSums.LocalField p) = _
  rw [MaskedQuotientCRT.localUnitPart_spec]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  change _ = (((MaskedQuotientCRT.localUnitPart C p
    (LocalFiniteSums.primeIdeal p) π hπ).val : LocalFiniteSums.LocalField p) ^
      MaskedQuotientCRT.primeExponent p I) * (u₀.val : LocalFiniteSums.LocalField p)
  rw [MaskedQuotientCRT.localUnitPart_spec, hp, pow_one, hu₀, hfree]
  change algebraMap F (LocalFiniteSums.LocalField p)
      ((π : F) ^ MaskedQuotientCRT.primeExponent p I * (x₀ : F)) / _ = _
  simp only [map_mul, map_pow, div_pow]
  ring

theorem prime_product_allowed
    (A : SArithmeticData F) (B : Subgroup A.V)
    (P : Finset (HeightOneSpectrum (𝓞 F)))
    (π : P → A.R) (aπ : P → Fˣ)
    (haπ : ∀ v : P, (aπ v : F) = (π v : F))
    (hπAllowed : ∀ v : P, A.IsAllowed B (aπ v)) (e : P → ℕ)
    (hne : (∏ v : P, π v ^ e v) ≠ 0) :
    A.IsAllowed B (Units.mk0 ((∏ v : P, π v ^ e v : A.R) : F)
      (by exact_mod_cast hne)) := by
  have he : Units.mk0 ((∏ v : P, π v ^ e v : A.R) : F)
      (by exact_mod_cast hne) = ∏ v : P, aπ v ^ e v := by
    apply Units.ext
    change ((∏ v : P, π v ^ e v : A.R) : F) =
      (Units.coeHom F) (∏ v : P, aπ v ^ e v)
    rw [map_prod]
    simp [haπ]
  rw [he]
  change A.sClass (∏ v : P, aπ v ^ e v) ∈ B
  rw [map_prod]
  have hall : ∀ T : Finset P, (∏ v ∈ T, A.sClass (aπ v ^ e v)) ∈ B := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using B.one_mem
    | @insert v T hv ih =>
      rw [Finset.prod_insert hv]
      exact B.mul_mem (by rw [map_pow]; exact B.pow_mem (hπAllowed v) _) ih
  exact hall Finset.univ

theorem masked_rescale_product_assembly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → ι → ℂ) (hβ : ∀ v w, w ≠ v → β v w ≠ 0)
    (θ C : ι → ℂ) (t k : ι → ℕ) :
    (∏ v : ι,
      θ v ^ ((k v : ℤ) - (t v : ℤ)) *
        (∏ w ∈ ({v}ᶜ : Finset ι), β v w ^ k w) ^ (t v : ℤ) *
        (∏ w ∈ ({v}ᶜ : Finset ι), β v w ^ t w) ^ ((t v : ℤ) - k v) * C v) =
      (∏ v : ι, θ v ^ ((k v : ℤ) - (t v : ℤ)) * C v) *
        (∏ v : ι, ∏ w ∈ ({v}ᶜ : Finset ι),
          β v w ^ ((t v : ℤ) * k w + ((t v : ℤ) - k v) * t w)) := by
  have hlocal (v : ι) :
      (∏ w ∈ ({v}ᶜ : Finset ι), β v w ^ k w) ^ (t v : ℤ) *
        (∏ w ∈ ({v}ᶜ : Finset ι), β v w ^ t w) ^ ((t v : ℤ) - k v) =
        ∏ w ∈ ({v}ᶜ : Finset ι),
          β v w ^ ((t v : ℤ) * k w + ((t v : ℤ) - k v) * t w) := by
    rw [← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro w hw
    have hwv : w ≠ v := by simpa using hw
    rw [← zpow_natCast (β v w) (k w), ← zpow_natCast (β v w) (t w),
      ← zpow_mul, ← zpow_mul, ← zpow_add₀ (hβ v w hwv)]
    congr 1
    ring
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  rw [← hlocal v]
  ring

theorem comparisonData_principal (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) : IsPrincipalIdealRing A.R := by
  constructor
  intro J
  by_cases hJ : J = ⊥
  · subst J; exact bot_isPrincipal
  let I : A.Exterior := A.exteriorIdealEquiv.symm ⟨J, hJ⟩
  have he : A.extendIdeal I = J := by
    rw [← A.exteriorIdealEquiv_apply]
    exact congrArg Subtype.val (A.exteriorIdealEquiv.apply_symm_apply ⟨J, hJ⟩)
  rw [← he, ← (D.generates I).2]
  infer_instance

theorem comparisonData_classGroup_trivial (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) : Subsingleton (ClassGroup A.R) := by
  letI := comparisonData_principal A D
  exact Fintype.card_le_one_iff_subsingleton.mp (by rw [card_classGroup_eq_one])

section AssemblyHelpers
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

def comparisonData_context
    (G : A.GaussCorrectionOutput σ η hS)
    (D : ComparisonPoissonCoefficientData F A) :
    A.GeneralArithmeticContext σ η hS := by
  letI := comparisonData_classGroup_trivial A D
  obtain ⟨hE, htwo, hthree⟩ :=
    ArithmeticContext.actual_hilbert_lagrangian_properties
      A (comparisonData_classGroup_trivial A D) G.H G.B G.H_actual G.B_complement
  exact {
    principal := comparisonData_principal A D
    classGroup_trivial := comparisonData_classGroup_trivial A D
    fractional_principal := fun I hI => exists_unit_of_isPrincipal I
      (ClassGroup.isPrincipal_coeSubmodule_of_isUnit I hI) hI.ne_zero
    unit_injective := A.unitQuotientClass_injective (comparisonData_classGroup_trivial A D)
    unit_image := A.unitQuotientClass_range
    correction := G
    units_lagrangian := hE
    primary_two := htwo
    primary_three := hthree
    reciprocity := ArithmeticContext.actual_hilbert_sextic_reciprocity
      A G.H G.B G.H_actual G.B_complement
    allowed_integral := fun I => A.exists_allowed_integral_generator
      (comparisonData_classGroup_trivial A D) G.H G.B G.B_complement I
    allowed_unique := fun I a b ha hb => A.allowed_generator_unique_mod_sixth
      (comparisonData_classGroup_trivial A D) G.H G.B G.B_complement I a b ha hb
    normOne_compact := ArithmeticContext.normOne_sixth_unit_quotient_compact A
    prime_target := fun I v hIv p hp a ha hap x hx =>
      G.prime_theta I v hIv p hp a ha hap x hx }

private theorem assembly_power_generates (p : LocalFiniteSums.ExteriorPrime A)
    (π : A.R) (hπ : A.Generates (LocalFiniteSums.primeIdeal p) π) (n : ℕ) :
    A.Generates (LocalFiniteSums.powerIdeal p n) (π ^ n) := by
  refine ⟨pow_ne_zero _ hπ.1, ?_⟩
  rw [← Ideal.span_singleton_pow, hπ.2]
  exact (Ideal.map_pow _ _ _).symm
private theorem assembly_exponent_power (p q : LocalFiniteSums.ExteriorPrime A) (n : ℕ) :
    MaskedQuotientCRT.primeExponent q (LocalFiniteSums.powerIdeal p n) =
      if q = p then n else 0 := by
  change (UniqueFactorizationMonoid.normalizedFactors (p.val.asIdeal ^ n)).count q.val.asIdeal = _
  rw [UniqueFactorizationMonoid.normalizedFactors_pow]
  simp only [UniqueFactorizationMonoid.normalizedFactors_irreducible p.val.irreducible,
    Multiset.count_nsmul, Multiset.count_singleton]
  by_cases h : q = p
  · simp [h]
  · have h' : q.val.asIdeal ≠ p.val.asIdeal := fun hh => h (Subtype.ext (HeightOneSpectrum.asIdeal_injective hh))
    simp [h, h', Ne.symm h']
private theorem assembly_power_allowed
    (C : A.GeneralArithmeticContext σ η hS) (p : LocalFiniteSums.ExteriorPrime A)
    (π : A.R) (hπ : A.Generates (LocalFiniteSums.primeIdeal p) π)
    (aπ : Fˣ) (haπ : (aπ : F) = (π : F)) (hAllowed : A.IsAllowed C.correction.B aπ)
    (n : ℕ) :
    A.IsAllowed C.correction.B (Units.mk0 ((π ^ n : A.R) : F)
      (by exact_mod_cast (assembly_power_generates p π hπ n).1)) := by
  have he : Units.mk0 ((π ^ n : A.R) : F)
      (by exact_mod_cast (assembly_power_generates p π hπ n).1) = aπ ^ n := by
    apply Units.ext
    simp [haπ]
  rw [he, SArithmeticData.IsAllowed, map_pow]
  exact C.correction.B.pow_mem hAllowed n
private theorem assembly_localUnit_power
    (C : A.GeneralArithmeticContext σ η hS) (p : LocalFiniteSums.ExteriorPrime A)
    (π : A.R) (hπ : A.Generates (LocalFiniteSums.primeIdeal p) π) (n : ℕ) :
    MaskedQuotientCRT.localUnitPart C p (LocalFiniteSums.powerIdeal p n) (π ^ n)
      (assembly_power_generates p π hπ n) =
      MaskedQuotientCRT.localUnitPart C p (LocalFiniteSums.primeIdeal p) π hπ ^ n := by
  have he := localUnitPart_primeFree_transport A σ η hS C p π hπ
    (LocalFiniteSums.powerIdeal p n) (π ^ n) 1 (assembly_power_generates p π hπ n)
    (by simp [assembly_exponent_power]) 1 (by simp)
  simpa [assembly_exponent_power] using he

theorem prime_generator_coefficient_eq_raw
    (C : A.GeneralArithmeticContext σ η hS)
    (D : ComparisonPoissonCoefficientData F A)
    (hCharacter : ∀ (I : A.Exterior) (a : A.R) (ha : A.Generates I a),
      D.character a = GeneratorInvariance.transportCharacter _ _ ha.2.symm
        (A.sexticResiduePowerChar σ I 1))
    (hTrace : ∀ x : F, D.additiveCharacter x = (A.fieldTraceCharacter x : ℂ))
    (p : LocalFiniteSums.ExteriorPrime A) (π : A.R)
    (hπ : A.Generates (LocalFiniteSums.primeIdeal p) π)
    (aπ : Fˣ) (haπ : (aπ : F) = (π : F)) (hAllowed : A.IsAllowed C.correction.B aπ)
    (t k J : ℕ) :
    GeneratorInvariance.coefficient A D (π ^ k) (π ^ t) (π ^ J)
      (pow_ne_zero _ hπ.1) (pow_ne_zero _ hπ.1) =
      let b := MaskedQuotientCRT.localUnitPart C p (LocalFiniteSums.primeIdeal p) π hπ
      CompatiblePrimeRawLocal.R C p t k J (b ^ k) (b ^ t) (b ^ J) := by
  rw [coefficient_eq_masked_crt A σ η hS D hCharacter hTrace C
    (LocalFiniteSums.powerIdeal p k) (LocalFiniteSums.powerIdeal p t)
    (π ^ k) (π ^ t) (π ^ J) (assembly_power_generates p π hπ k)
    (assembly_power_generates p π hπ t)]
  have hsupp : ∀ n : ℕ, ∀ q : LocalFiniteSums.ExteriorPrime A,
      MaskedQuotientCRT.primeExponent q (LocalFiniteSums.powerIdeal p n) ≠ 0 → q ∈ ({p} : Finset _) := by
    intro n q hq
    simp only [assembly_exponent_power] at hq
    split_ifs at hq with he
    · simpa using he
    · exact (hq rfl).elim
  have hc := MaskedQuotientCRT.full_prime_power_crt C
    (LocalFiniteSums.powerIdeal p k) (LocalFiniteSums.powerIdeal p t) (LocalFiniteSums.powerIdeal p J)
    (π ^ k) (π ^ t) (π ^ J) (assembly_power_generates p π hπ k)
    (assembly_power_generates p π hπ t) (assembly_power_generates p π hπ J)
    (assembly_power_allowed C p π hπ aπ haπ hAllowed k)
    (assembly_power_allowed C p π hπ aπ haπ hAllowed t) {p}
    (hsupp k) (hsupp t) (hsupp J)
  simp only [Finset.prod_singleton, assembly_exponent_power, ite_true] at hc
  rw [assembly_localUnit_power C p π hπ k, assembly_localUnit_power C p π hπ t,
    assembly_localUnit_power C p π hπ J] at hc
  exact hc

end AssemblyHelpers

theorem masked_product_assembly
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (G : A.GaussCorrectionOutput σ η hS)
    (D : ComparisonPoissonCoefficientData F A)
    (hCharacter : ∀ (I : A.Exterior) (a : A.R) (ha : A.Generates I a),
      D.character a = GeneratorInvariance.transportCharacter _ _ ha.2.symm
        (A.sexticResiduePowerChar σ I 1))
    (hTrace : ∀ x : F, D.additiveCharacter x = (A.fieldTraceCharacter x : ℂ))
    (Ic In Is Ir Iu : A.Exterior) (u : A.R) (hu : A.Generates Iu u)
    (P : Finset (HeightOneSpectrum (𝓞 F)))
    (p : P → A.Exterior) (hp : ∀ v : P, (p v).val = v.val.asIdeal)
    (π : P → A.R) (hπ : ∀ v : P, A.Generates (p v) (π v))
    (aπ : P → Fˣ) (haπ : ∀ v : P, (aπ v : F) = (π v : F))
    (hπAllowed : ∀ v : P, A.IsAllowed G.B (aπ v))
    (hSupport : ∀ I ∈ ({Ic, In, Is, Ir, Iu} : Finset A.Exterior),
      I.val = ∏ v : P, v.val.asIdeal ^ idealPrimeExponent v.val.asIdeal I.val)
    (uPrimeFree : P → A.R)
    (hPrimeFree : ∀ v : P,
      u = π v ^ idealPrimeExponent v.val.asIdeal Iu.val * uPrimeFree v)
    (hPrimeUnit : ∀ v : P,
      IsUnit (Ideal.Quotient.mk (A.extendIdeal (p v)) (uPrimeFree v))) :
    GeneratorInvariance.coefficient A D
        (∏ v : P, π v ^ idealPrimeExponent v.val.asIdeal Is.val)
        (∏ v : P, π v ^ (idealPrimeExponent v.val.asIdeal Ic.val +
          3 * idealPrimeExponent v.val.asIdeal In.val))
        (u * (∏ v : P, π v ^ idealPrimeExponent v.val.asIdeal Ir.val) ^ 6)
        (Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ (hπ v).1))
        (Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ (hπ v).1)) =
      (∏ v : P,
        let t := idealPrimeExponent v.val.asIdeal Ic.val +
          3 * idealPrimeExponent v.val.asIdeal In.val
        let k := idealPrimeExponent v.val.asIdeal Is.val
        let J := idealPrimeExponent v.val.asIdeal Iu.val +
          6 * idealPrimeExponent v.val.asIdeal Ir.val
        σ (A.sexticResidue (p v) (uPrimeFree v)) ^ ((k : ℤ) - (t : ℤ)) *
          GeneratorInvariance.coefficient A D (π v ^ k) (π v ^ t) (π v ^ J)
            (pow_ne_zero _ (hπ v).1) (pow_ne_zero _ (hπ v).1)) *
      (∏ v : P, ∏ w ∈ ({v}ᶜ : Finset P),
        σ (A.sexticResidue (p v) (π w)) ^
          (((idealPrimeExponent v.val.asIdeal Ic.val +
              3 * idealPrimeExponent v.val.asIdeal In.val : ℕ) : ℤ) *
              idealPrimeExponent w.val.asIdeal Is.val +
            (((idealPrimeExponent v.val.asIdeal Ic.val +
                3 * idealPrimeExponent v.val.asIdeal In.val : ℕ) : ℤ) -
                idealPrimeExponent v.val.asIdeal Is.val) *
              (idealPrimeExponent w.val.asIdeal Ic.val +
                3 * idealPrimeExponent w.val.asIdeal In.val))) := by
  let C := comparisonData_context G D
  let k := fun v : P => idealPrimeExponent v.val.asIdeal Is.val
  let t := fun v : P => idealPrimeExponent v.val.asIdeal Ic.val +
    3 * idealPrimeExponent v.val.asIdeal In.val
  let j := fun v : P => idealPrimeExponent v.val.asIdeal Iu.val
  let l := fun v : P => idealPrimeExponent v.val.asIdeal Ir.val
  let q := MaskedProductAssembly.indexedPrime A P p hp
  let β := fun v w : P => σ (A.sexticResidue (p v) (π w))
  let θ := fun v : P => σ (A.sexticResidue (p v) (uPrimeFree v))
  let L := fun v : P => GeneratorInvariance.coefficient A D
    (π v ^ k v) (π v ^ t v) (π v ^ (j v + 6 * l v))
    (pow_ne_zero _ (hπ v).1) (pow_ne_zero _ (hπ v).1)
  obtain ⟨Ia, Ih, hs, ha, hh, hdepth, hcoverage⟩ :=
    MaskedProductAssembly.prime_product_assembly_data
      A Ic In Is Ir Iu u hu P p hp π hπ hSupport 3 6
  have hsAllowed : A.IsAllowed C.correction.B
      (Units.mk0 ((∏ v : P, π v ^ k v : A.R) : F)
        (by exact_mod_cast hs.1)) :=
    prime_product_allowed A G.B P π aπ haπ hπAllowed k hs.1
  have haAllowed : A.IsAllowed C.correction.B
      (Units.mk0 ((∏ v : P, π v ^ t v : A.R) : F)
        (by exact_mod_cast ha.1)) :=
    prime_product_allowed A G.B P π aπ haπ hπAllowed t ha.1
  have hcrt := MaskedProductAssembly.indexed_coefficient_crt
    A σ η hS C D hCharacter hTrace Is Ia Ih
    (∏ v : P, π v ^ k v) (∏ v : P, π v ^ t v)
    (u * (∏ v : P, π v ^ l v) ^ 6) hs ha hh hsAllowed haAllowed
    P p hp hcoverage
  have hsingle (v : P) : L v =
      let b := MaskedQuotientCRT.localUnitPart C (q v)
        (LocalFiniteSums.primeIdeal (q v)) (π v)
        (by simpa [q] using hπ v)
      CompatiblePrimeRawLocal.R C (q v) (t v) (k v) (j v + 6 * l v)
        (b ^ k v) (b ^ t v) (b ^ (j v + 6 * l v)) := by
    exact prime_generator_coefficient_eq_raw C D hCharacter hTrace
      (q v) (π v) (by simpa [q] using hπ v) (aπ v) (haπ v)
      (hπAllowed v) (t v) (k v) (j v + 6 * l v)
  have hlocal (v : P) := MaskedProductAssembly.prime_product_local_rescale
    A σ η hS C P p hp π hπ t k j l u Is Ia Ih hs ha hh hdepth
    uPrimeFree hPrimeFree hPrimeUnit v
  change GeneratorInvariance.coefficient A D
      (∏ v : P, π v ^ k v) (∏ v : P, π v ^ t v)
      (u * (∏ v : P, π v ^ l v) ^ 6) _ _ =
    (∏ v : P, θ v ^ ((k v : ℤ) - t v) * L v) *
      (∏ v : P, ∏ w ∈ ({v}ᶜ : Finset P),
        β v w ^ ((t v : ℤ) * k w + ((t v : ℤ) - k v) * t w))
  rw [hcrt]
  calc
    _ = ∏ v : P,
        θ v ^ ((k v : ℤ) - t v) *
          (∏ w ∈ ({v}ᶜ : Finset P), β v w ^ k w) ^ (t v : ℤ) *
          (∏ w ∈ ({v}ᶜ : Finset P), β v w ^ t w) ^ ((t v : ℤ) - k v) * L v := by
      apply Finset.prod_congr rfl
      intro v _
      rw [(hdepth v).1, (hdepth v).2.1, (hdepth v).2.2]
      rw [hlocal v, hsingle v]
    _ = _ := masked_rescale_product_assembly β
      (MaskedProductAssembly.cross_prime_residue_ne_zero A σ P p hp π hπ) θ L t k

end
end DedekindZetaZeroFree.GaussProductCancellation

end
