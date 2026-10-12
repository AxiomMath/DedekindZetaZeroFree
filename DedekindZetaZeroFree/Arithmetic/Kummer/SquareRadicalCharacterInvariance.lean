module

public import DedekindZetaZeroFree.Arithmetic.Kummer.PrincipalProductAndPrimeFrobenius
public import DedekindZetaZeroFree.Arithmetic.Kummer.SquareConductorInvariance

@[expose] public section

namespace DedekindZetaZeroFree.RMKummerSquareCharacter

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

private theorem prime_eq_lambda (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F))
    (hc : v.asIdeal ⊔ RMKummerConductor.m F h12 x = ⊤)
    (π : (v.adicCompletion F)ˣ)
    (hπ : HeightOneSpectrum.adicCompletion.valuation F v (π : v.adicCompletion F) =
      WithZero.exp (-1 : ℤ)) :
    RMKummerConductor.Xi F h12 x v.asIdeal =
      (RMKummerLocalNormCharacter.lambda F h12 x v π : ℂ) := by
  have hd : ¬ v.asIdeal ∣ RMKummerConductor.m F h12 x := by
    intro h
    rw [Ideal.dvd_iff_le] at h
    exact v.isPrime.ne_top ((sup_of_le_left h).symm.trans hc)
  have hs : v ∉ (M F (RMKummerConductor.m F h12 x)
      (RMKummerConductor.m_ne_bot F h12 x)).finitePart.support := by
    rw [Finsupp.notMem_support_iff, M_finitePart, idealPrimeExponent,
      Multiset.count_eq_zero, UniqueFactorizationMonoid.mem_normalizedFactors_iff
        (RMKummerConductor.m_ne_bot F h12 x)]
    exact fun h => hd h.2
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 (RMKummerConductor.E F h12 x)) v.asIdeal
  letI : Q.LiesOver v.asIdeal := hQover
  let w : HeightOneSpectrum (𝓞 (RMKummerConductor.E F h12 x)) :=
    ⟨Q, hQmax.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  rw [RMKummerPrincipalPrime.prime_arithmeticFrobenius F h12 x v hs w hQover,
    RMKummerPrincipalPrime.arithmeticFrobenius_eq_lambda_uniformizer
      F h12 x v hs w hQover π hπ]

private theorem exists_uniformizer (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : (v.adicCompletion F)ˣ,
      HeightOneSpectrum.adicCompletion.valuation F v (π : v.adicCompletion F) =
        WithZero.exp (-1 : ℤ) := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v
    (WithZero.exp (-1 : ℤ))
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  exact ⟨Units.mk0 a ha0, ha⟩

theorem Xi_mul_sq (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x y : Fˣ)
    (I : Ideal (𝓞 F)) :
    RMKummerConductor.Xi F h12 (x * y ^ 2) I =
      RMKummerConductor.Xi F h12 x I := by
  have hm := RMKummerSquareConductor.m_mul_sq F h12 x y
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
      change RMKummerConductor.Xi F h12 (x * y ^ 2) ⊥ = RMKummerConductor.Xi F h12 x ⊥
      rw [(RMKummerConductor.Xi F h12 (x * y ^ 2)).eq_zero_iff' _ |>.mpr (Or.inl rfl),
        (RMKummerConductor.Xi F h12 x).eq_zero_iff' _ |>.mpr (Or.inl rfl)]
  | h₂ J hJ =>
      rw [Ideal.isUnit_iff.mp hJ]
      exact (RMKummerConductor.Xi F h12 (x * y ^ 2)).map_top'.trans
        (RMKummerConductor.Xi F h12 x).map_top'.symm
  | h₃ J P hJ hP ih =>
      rw [(RMKummerConductor.Xi F h12 (x * y ^ 2)).map_mul',
        (RMKummerConductor.Xi F h12 x).map_mul', ih]
      congr 1
      by_cases hc : P ⊔ RMKummerConductor.m F h12 x = ⊤
      · let v : HeightOneSpectrum (𝓞 F) := ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩
        obtain ⟨π, hπ⟩ := exists_uniformizer F v
        have hc' : v.asIdeal ⊔ RMKummerConductor.m F h12 (x * y ^ 2) = ⊤ := by
          simpa only [hm] using hc
        rw [prime_eq_lambda F h12 (x * y ^ 2) v hc' π hπ,
          prime_eq_lambda F h12 x v hc π hπ,
          RMKummerLocalSquareLaws.lambda_mul_sq]
      · have hc' : P ⊔ RMKummerConductor.m F h12 (x * y ^ 2) ≠ ⊤ := by
          simpa only [hm] using hc
        rw [(RMKummerConductor.Xi F h12 (x * y ^ 2)).eq_zero_iff' _ |>.mpr (Or.inr hc'),
          (RMKummerConductor.Xi F h12 x).eq_zero_iff' _ |>.mpr (Or.inr hc)]

theorem Xi_cube (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (I : Ideal (𝓞 F)) :
    (RMKummerConductor.Xi F h12 x I) ^ 3 =
      RMKummerConductor.Xi F h12 x I := by
  by_cases h : I ≠ ⊥ ∧ I ⊔ RMKummerConductor.m F h12 x = ⊤
  · change frozenRayValue F _ _ _ I ^ 3 = frozenRayValue F _ _ _ I
    rw [frozenRayValue_of_primeTo F _ _ _ I h.1 h.2]
    have hs : (RMKummerConductor.rho F h12 x
        (frozenIntegralRayClass F _ _ I h.1 h.2)) ^ 2 = 1 := by
      unfold RMKummerConductor.rho RMKummerConductor.kappa
      exact rmKummerQuadraticRootsComplexMap_pow_two F h12 _ _
    have hs' : (RMKummerConductor.rho F h12 x
        (frozenIntegralRayClass F _ _ I h.1 h.2) : ℂ) ^ 2 = 1 :=
      congrArg (fun z : ℂˣ => (z : ℂ)) hs
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hs', one_mul]
  · have hz : RMKummerConductor.Xi F h12 x I = 0 :=
      (RMKummerConductor.Xi F h12 x).eq_zero_iff' I |>.mpr (by tauto)
    simp [hz]

theorem Xi_one (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (I : Ideal (𝓞 F)) :
    RMKummerConductor.Xi F h12 (1 : Fˣ) I =
      if I = ⊥ then (0 : ℂ) else 1 := by
  have hm := RMKummerSquareConductor.m_one F h12
  by_cases hb : I = ⊥
  · rw [if_pos hb]
    exact (RMKummerConductor.Xi F h12 1).eq_zero_iff' I |>.mpr (Or.inl hb)
  · rw [if_neg hb]
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => exact (hb rfl).elim
    | h₂ J hJ =>
        rw [Ideal.isUnit_iff.mp hJ]
        exact (RMKummerConductor.Xi F h12 1).map_top'
    | h₃ J P hJ hP ih =>
        rw [(RMKummerConductor.Xi F h12 1).map_mul', ih hJ, mul_one]
        let v : HeightOneSpectrum (𝓞 F) := ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩
        obtain ⟨π, hπ⟩ := exists_uniformizer F v
        have hc : v.asIdeal ⊔ RMKummerConductor.m F h12 1 = ⊤ := by
          rw [hm, sup_top_eq]
        rw [prime_eq_lambda F h12 1 v hc π hπ,
          RMKummerLocalSquareLaws.lambda_one, Units.val_one]

end
end DedekindZetaZeroFree.RMKummerSquareCharacter
