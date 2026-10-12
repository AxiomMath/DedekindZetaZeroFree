module

public import DedekindZetaZeroFree.Arithmetic.Ideals.PrincipalDivisibilityByValuation
public import DedekindZetaZeroFree.Arithmetic.LocalFields.ValuationRings.PrincipalIdeals
public import DedekindZetaZeroFree.Arithmetic.LocalFields.Approximation.IntegralCompletion

@[expose] public section

open scoped NumberField Classical Valued
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSumCompatibility
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem integerMap_mem (p : ExteriorPrime A) (x : A.R) :
    algebraMap F (LocalField p) (x : F) ∈ p.val.adicCompletionIntegers F := by
  have hp : p.val ∉ A.Sf := by
    intro hp
    have h := (A.exterior_iff ⟨p.val.asIdeal, p.val.ne_bot⟩).mp p.property p.val hp
    rw [sup_idem] at h
    exact p.val.isPrime.ne_top h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact Set.integer_valuation_le_one _ _ x hp

def integerMap (p : ExteriorPrime A) : A.R →+* LocalIntegers p where
  toFun x := ⟨algebraMap F (LocalField p) (x : F), integerMap_mem p x⟩
  map_one' := by apply Subtype.ext; simp
  map_zero' := by apply Subtype.ext; simp
  map_add' x y := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

def localUniformizer (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) : LocalIntegers p := integerMap p (generator C p)

abbrev LocalResidue (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :=
  FiniteTransform.Residue (p.val.adicCompletionIntegers F).toSubring (localUniformizer C p ^ n)

theorem denominator_le_comap (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    Ideal.span {generator C p ^ n} ≤
      (Ideal.span {localUniformizer C p ^ n}).comap (integerMap p) := by
  apply Ideal.span_le.mpr
  rintro x (rfl : x = generator C p ^ n)
  change integerMap p (generator C p ^ n) ∈ Ideal.span {localUniformizer C p ^ n}
  rw [map_pow]
  exact Ideal.subset_span (Set.mem_singleton _)

def quotientMap (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) : Residue C p n →+* LocalResidue C p n :=
  Ideal.quotientMap (Ideal.span {localUniformizer C p ^ n}) (integerMap p)
    (denominator_le_comap C p n)

theorem uniformizer_valuation (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) :
    (Valued.v : Valuation (LocalField p) (WithZero (Multiplicative ℤ)))
      (uniformizer C p) = WithZero.exp (-1 : ℤ) := by
  have hp : p.val ∉ A.Sf := by
    intro hp
    have h := (A.exterior_iff ⟨p.val.asIdeal, p.val.ne_bot⟩).mp p.property p.val hp
    rw [sup_idem] at h
    exact p.val.isPrime.ne_top h
  rw [uniformizer, HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have h := SIntegerLocalization.generator_valuation A.Sf (primeIdeal p).val
    (primeIdeal p).property.1 (generator C p) (generator_generates C p).1
    (generator_generates C p).2 p.val hp
  have hf : UniqueFactorizationMonoid.normalizedFactors p.val.asIdeal = {p.val.asIdeal} := by
    simpa using p.val.irreducible.normalizedFactors_pow 1
  simpa [idealPrimeExponent, primeIdeal, hf] using h

theorem quotientMap_bijective (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) : Function.Bijective (quotientMap C p n) := by
  have hval : Valued.v ((localUniformizer C p ^ n : LocalIntegers p) : LocalField p) =
      WithZero.exp (-(n : ℤ)) := by
    change Valued.v (uniformizer C p ^ n) = _
    rw [map_pow, uniformizer_valuation]
    simp [← WithZero.exp_nsmul, nsmul_eq_mul]
  have hnz : ((localUniformizer C p ^ n : LocalIntegers p) : LocalField p) ≠ 0 := by
    intro h
    rw [h, map_zero] at hval
    exact WithZero.exp_ne_zero hval.symm
  have local_mem (x : LocalIntegers p) :
      x ∈ Ideal.span {localUniformizer C p ^ n} ↔
      Valued.v (x : LocalField p) ≤ WithZero.exp (-(n : ℤ)) := by
    exact (valuationInteger_mem_span_iff (Valued.v) _ _ hnz).trans
      (by rw [hval])
  constructor
  · apply (RingHom.injective_iff_ker_eq_bot _).mpr
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hm : integerMap p r ∈ Ideal.span {localUniformizer C p ^ n} := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact hx
    have hv := (local_mem (integerMap p r)).mp hm
    change Valued.v (algebraMap F (LocalField p) (r : F)) ≤ _ at hv
    rw [HeightOneSpectrum.algebraMap_adicCompletion] at hv
    simp only [Function.comp_apply, Algebra.algebraMap_self] at hv
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((globalDenominator_mem_iff C p n r).mpr hv)
  · intro x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, ha⟩ := completion_integer_approximation p.val z n
    refine ⟨residueMap C p n (algebraMap (𝓞 F) A.R a), ?_⟩
    apply Ideal.Quotient.eq.mpr
    apply (local_mem _).mpr
    exact ha

def residueEquiv (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) : Residue C p n ≃+* LocalResidue C p n :=
  RingEquiv.ofBijective (quotientMap C p n) (quotientMap_bijective C p n)

theorem residueEquiv_mk (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (x : A.R) :
    residueEquiv C p n (residueMap C p n x) =
      FiniteTransform.residueMap (p.val.adicCompletionIntegers F).toSubring
        (localUniformizer C p ^ n) (integerMap p x) := by
  change quotientMap C p n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (integerMap p x)
  simp only [quotientMap, Ideal.quotientMap_mk]
  rfl

end DedekindZetaZeroFree.LocalFiniteSumCompatibility

end
