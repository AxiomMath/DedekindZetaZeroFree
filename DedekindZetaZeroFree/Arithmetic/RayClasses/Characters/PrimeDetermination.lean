module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.AbelianQuotient

theorem rayCharacterIntegralPrimeReduction
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (χ : DedekindZetaZeroFree.RayClassCharacter K m)
    (H : ClassFieldTheory.NumberFieldFractionalIdealGroup K →* ℂˣ)
    (hprime : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      χ v.asIdeal ≠ 0 →
        (H (ClassFieldTheory.finitePrimeFractionalIdeal v) : ℂ) = χ v.asIdeal) :
    ∀ I : Ideal (𝓞 K), χ I ≠ 0 →
      ∀ J : ClassFieldTheory.NumberFieldFractionalIdealGroup K,
        (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
          (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) →
        (H J : ℂ) = χ I := by
  classical
  let P : Ideal (𝓞 K) → Prop := fun I =>
    χ I ≠ 0 → ∀ J : ClassFieldTheory.NumberFieldFractionalIdealGroup K,
      (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) →
      (H J : ℂ) = χ I
  have hP : ∀ I, P I := by
    intro I
    refine UniqueFactorizationMonoid.induction_on_prime I ?h0 ?hunit ?hstep
    · intro hzero
      exact absurd ((χ.eq_zero_iff' 0).mpr (Or.inl rfl)) hzero
    · intro x hx hxne J hJ
      have hxtop : x = ⊤ := Ideal.isUnit_iff.mp hx
      have hJone : J = 1 := Units.ext (by
        rw [hJ, hxtop, FractionalIdeal.coeIdeal_top, Units.val_one])
      rw [hJone, map_one, hxtop]
      simp [χ.map_top']
    · intro a p ha0 hp hPa hne J hJ
      rw [χ.map_mul'] at hne
      have hpne : χ p ≠ 0 := fun h => hne (by rw [h, zero_mul])
      have hane : χ a ≠ 0 := fun h => hne (by rw [h, mul_zero])
      have hp0 : p ≠ 0 := hp.ne_zero
      have hprime_p : p.IsPrime := (Ideal.prime_iff_isPrime hp0).mp hp
      let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨p, hprime_p, hp0⟩
      let A : ClassFieldTheory.NumberFieldFractionalIdealGroup K :=
        Units.mk0 (a : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
          (FractionalIdeal.coeIdeal_ne_zero.mpr ha0)
      have hAval : (A : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
          (a : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
        simp only [A, Units.val_mk0]
      have hJA : J = ClassFieldTheory.finitePrimeFractionalIdeal v * A := by
        apply Units.ext
        rw [Units.val_mul, hAval, hJ, FractionalIdeal.coeIdeal_mul]
        congr 1
      rw [hJA, map_mul, Units.val_mul, hprime v hpne, hPa hane A hAval, χ.map_mul']
  exact fun I hI J hJ => hP I hI J hJ

end DedekindZetaZeroFree.AbelianQuotient
