module

public import DedekindZetaZeroFree.Arithmetic.Kummer.LeastLocalConductorExponent
public import DedekindZetaZeroFree.Arithmetic.Kummer.LocalQuadraticCharacterLaws

@[expose] public section

namespace DedekindZetaZeroFree.RMKummerSquareConductor

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

private theorem ideal_eq_of_exponents (F : Type) [Field F] [NumberField F]
    (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (h : ∀ v : HeightOneSpectrum (𝓞 F),
      idealPrimeExponent v.asIdeal I = idealPrimeExponent v.asIdeal J) : I = J := by
  rw [← Ideal.iInf_maxPowDividing_eq hI, ← Ideal.iInf_maxPowDividing_eq hJ]
  apply iInf_congr
  intro v
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count v hI,
    HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count v hJ]
  exact congrArg (fun n => v.asIdeal ^ n) (h v)

theorem isLeast_mul_sq_iff (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x y : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    IsLeast (fun k : ℕ =>
      ClassFieldTheory.rayLocalHigherUnitGroup v k ≤
        (RMKummerLocalNormCharacter.lambda F h12 (x * y ^ 2) v).ker) n ↔
    IsLeast (fun k : ℕ =>
      ClassFieldTheory.rayLocalHigherUnitGroup v k ≤
        (RMKummerLocalNormCharacter.lambda F h12 x v).ker) n := by
  have hchar : RMKummerLocalNormCharacter.lambda F h12 (x * y ^ 2) v =
      RMKummerLocalNormCharacter.lambda F h12 x v := by
    apply MonoidHom.ext
    intro t
    exact RMKummerLocalSquareLaws.lambda_mul_sq F h12 x y v t
  rw [hchar]

theorem finiteExponent_mul_sq (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x y : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (M F (RMKummerConductor.m F h12 (x * y ^ 2))
      (RMKummerConductor.m_ne_bot F h12 (x * y ^ 2))).finitePart v =
    (M F (RMKummerConductor.m F h12 x)
      (RMKummerConductor.m_ne_bot F h12 x)).finitePart v := by
  exact ((isLeast_mul_sq_iff F h12 x y v _).mp
    (RMKummerLeastLocalExponent.finiteExponent_isLeast F h12 (x * y ^ 2) v)).unique
      (RMKummerLeastLocalExponent.finiteExponent_isLeast F h12 x v)

theorem m_mul_sq (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x y : Fˣ) :
    RMKummerConductor.m F h12 (x * y ^ 2) = RMKummerConductor.m F h12 x := by
  apply ideal_eq_of_exponents F _ _
    (RMKummerConductor.m_ne_bot F h12 (x * y ^ 2))
    (RMKummerConductor.m_ne_bot F h12 x)
  intro v
  simpa only [RMKummerLeastLocalExponent.finiteExponent_eq_ord] using
    finiteExponent_mul_sq F h12 x y v

theorem m_one (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) :
    RMKummerConductor.m F h12 (1 : Fˣ) = ⊤ := by
  apply ideal_eq_of_exponents F _ _ (RMKummerConductor.m_ne_bot F h12 1) top_ne_bot
  intro v
  have hzero : ClassFieldTheory.rayLocalHigherUnitGroup v 0 ≤
      (RMKummerLocalNormCharacter.lambda F h12 1 v).ker := by
    intro t _
    exact MonoidHom.mem_ker.mpr (RMKummerLocalSquareLaws.lambda_one F h12 v t)
  have hle := (RMKummerLeastLocalExponent.finiteExponent_isLeast F h12 1 v).2 hzero
  rw [RMKummerLeastLocalExponent.finiteExponent_eq_ord] at hle
  have heq := Nat.eq_zero_of_le_zero hle
  rw [heq]
  unfold idealPrimeExponent
  rw [← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one,
    Multiset.count_zero]

end
end DedekindZetaZeroFree.RMKummerSquareConductor
