module

public import DedekindZetaZeroFree.Arithmetic.Kummer.LocalQuadraticCharacterLaws
public import DedekindZetaZeroFree.Arithmetic.Kummer.PrincipalProductAndPrimeFrobenius

@[expose] public section

namespace DedekindZetaZeroFree.RMKummerQuotientPrime

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

private theorem prime_eq_lambda (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ RMKummerConductor.m F h12 x)
    (π : (v.adicCompletion F)ˣ)
    (hπ : HeightOneSpectrum.adicCompletion.valuation F v (π : v.adicCompletion F) =
      WithZero.exp (-1 : ℤ)) :
    RMKummerConductor.Xi F h12 x v.asIdeal =
      (RMKummerLocalNormCharacter.lambda F h12 x v π : ℂ) := by
  have hs : v ∉ (M F (RMKummerConductor.m F h12 x)
      (RMKummerConductor.m_ne_bot F h12 x)).finitePart.support := by
    rw [Finsupp.notMem_support_iff, M_finitePart, idealPrimeExponent,
      Multiset.count_eq_zero, UniqueFactorizationMonoid.mem_normalizedFactors_iff
        (RMKummerConductor.m_ne_bot F h12 x)]
    exact fun h => hv h.2
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 (RMKummerConductor.E F h12 x)) v.asIdeal
  letI : Q.LiesOver v.asIdeal := hQover
  let w : HeightOneSpectrum (𝓞 (RMKummerConductor.E F h12 x)) :=
    ⟨Q, hQmax.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  rw [RMKummerPrincipalPrime.prime_arithmeticFrobenius F h12 x v hs w hQover,
    RMKummerPrincipalPrime.arithmeticFrobenius_eq_lambda_uniformizer
      F h12 x v hs w hQover π hπ]

theorem quotient_prime (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x y : Fˣ)
    (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ v.asIdeal ∣ RMKummerConductor.m F h12 x *
      RMKummerConductor.m F h12 y * RMKummerConductor.m F h12 (x / y)) :
    RMKummerConductor.Xi F h12 (x / y) v.asIdeal =
      RMKummerConductor.Xi F h12 x v.asIdeal *
        star (RMKummerConductor.Xi F h12 y v.asIdeal) := by
  have hx : ¬ v.asIdeal ∣ RMKummerConductor.m F h12 x := by
    intro h
    exact hv (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left h (RMKummerConductor.m F h12 y))
      (RMKummerConductor.m F h12 (x / y)))
  have hy : ¬ v.asIdeal ∣ RMKummerConductor.m F h12 y := by
    intro h
    exact hv (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right h (RMKummerConductor.m F h12 x))
      (RMKummerConductor.m F h12 (x / y)))
  have hxy : ¬ v.asIdeal ∣ RMKummerConductor.m F h12 (x / y) := by
    intro h
    exact hv (dvd_mul_of_dvd_right h
      (RMKummerConductor.m F h12 x * RMKummerConductor.m F h12 y))
  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v
    (WithZero.exp (-1 : ℤ))
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  let π : (v.adicCompletion F)ˣ := Units.mk0 a ha0
  have hπ : HeightOneSpectrum.adicCompletion.valuation F v (π : v.adicCompletion F) =
      WithZero.exp (-1 : ℤ) := ha
  rw [prime_eq_lambda F h12 (x / y) v hxy π hπ,
    prime_eq_lambda F h12 x v hx π hπ, prime_eq_lambda F h12 y v hy π hπ]
  have h := congrArg Units.val (RMKummerLocalSquareLaws.lambda_div F h12 x y v π)
  simpa only [Units.val_mul, RMKummerLocalSquareLaws.lambda_inv_eq_conj] using h

end
end DedekindZetaZeroFree.RMKummerQuotientPrime
