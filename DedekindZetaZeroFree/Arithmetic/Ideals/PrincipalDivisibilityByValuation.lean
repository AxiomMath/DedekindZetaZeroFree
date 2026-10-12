module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.LocalSeriesDefinitions

@[expose] public section

open scoped NumberField Classical WithZero
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSumCompatibility
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem globalDenominator_mem_iff (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (x : A.R) :
    x ∈ Ideal.span {generator C p ^ n} ↔
      p.val.valuation F (x : F) ≤ WithZero.exp (-(n : ℤ)) := by
  have hg : (generator C p : F) ≠ 0 := fun h =>
    (generator_generates C p).1 (Subtype.ext h)
  have hv (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
      v.valuation F (generator C p : F) =
        WithZero.exp (-(if v = p.val then 1 else 0 : ℕ) : ℤ) := by
    have h := SIntegerLocalization.generator_valuation A.Sf (primeIdeal p).val
      (primeIdeal p).property.1 (generator C p) (generator_generates C p).1
      (generator_generates C p).2 v hv
    have hf : UniqueFactorizationMonoid.normalizedFactors p.val.asIdeal = {p.val.asIdeal} := by
      simpa using p.val.irreducible.normalizedFactors_pow 1
    simpa [idealPrimeExponent, primeIdeal, hf, Multiset.count_singleton,
      HeightOneSpectrum.ext_iff] using h
  have hp : p.val ∉ A.Sf := by
    intro hp
    have h := (A.exterior_iff ⟨p.val.asIdeal, p.val.ne_bot⟩).mp p.property p.val hp
    rw [sup_idem] at h
    exact p.val.isPrime.ne_top h
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
    have he := congrArg (fun z : A.R => (z : F)) hy
    change (x : F) = (generator C p : F) ^ n * (y : F) at he
    rw [he, map_mul, map_pow, hv p.val hp]
    simp only [if_pos rfl, Nat.cast_one, ← WithZero.exp_nsmul, neg_one_mul]
    exact (mul_le_mul_of_nonneg_left (y.property p.val hp) zero_le).trans (by simp)
  · intro hx
    let y : A.R := ⟨(x : F) / (generator C p : F) ^ n, by
      intro v hvS
      rw [map_div₀, map_pow, hv v hvS]
      by_cases h : v = p.val
      · subst v
        simp only [↓reduceIte, Nat.cast_one, ← WithZero.exp_nsmul, nsmul_eq_mul,
          mul_neg, mul_one]
        exact (div_le_one₀ WithZero.exp_pos).mpr hx
      · simpa [h] using x.property v hvS⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change (x : F) = (generator C p : F) ^ n * ((x : F) / (generator C p : F) ^ n)
    field_simp
end DedekindZetaZeroFree.LocalFiniteSumCompatibility

end
