module

public import DedekindZetaZeroFree.Arithmetic.Kummer.QuotientRadicalPrimeValues
public import DedekindZetaZeroFree.Arithmetic.Kummer.SquareRadicalCharacterInvariance

@[expose] public section

namespace DedekindZetaZeroFree.RMKummerCharacterAPI

noncomputable section
open scoped NumberField Classical TensorProduct
open IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty)

abbrev E (x : Fˣ) : IntermediateField F (SeparableClosure F) :=
  RMKummerConductor.E F h12 x

abbrev m (x : Fˣ) : Ideal (𝓞 F) := RMKummerConductor.m F h12 x

abbrev lambda (x : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* ℂˣ := RMKummerLocalNormCharacter.lambda F h12 x v

theorem local_character (x : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (lambda F h12 x v : (v.adicCompletion F)ˣ → ℂˣ) ∧
    (∀ t : (v.adicCompletion F)ˣ, lambda F h12 x v t ^ 2 = 1) ∧
    (lambda F h12 x v).ker =
      ClassFieldTheory.finitePlaceTensorNormSubgroup F (E F h12 x) v ∧
    (lambda F h12 x v).ker =
      (Units.map (Algebra.norm (v.adicCompletion F)
        (S := v.adicCompletion F ⊗[F] E F h12 x))).range := by
  exact ⟨RMKummerLocalNormCharacter.lambda_continuous F h12 x v,
    RMKummerLocalNormCharacter.lambda_pow_two F h12 x v,
    RMKummerLocalNormCharacter.lambda_ker F h12 x v,
    RMKummerLocalNormCharacter.lambda_ker_eq_norm_range F h12 x v⟩

theorem local_conductor (x : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    IsLeast (fun n : ℕ => ClassFieldTheory.rayLocalHigherUnitGroup v n ≤
      (lambda F h12 x v).ker) (idealPrimeExponent v.asIdeal (m F h12 x)) := by
  simpa only [RMKummerLeastLocalExponent.finiteExponent_eq_ord] using
    RMKummerLeastLocalExponent.finiteExponent_isLeast F h12 x v

theorem local_trivial_on_conductor (x : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (t : (v.adicCompletion F)ˣ)
    (ht : t ∈ ClassFieldTheory.rayLocalHigherUnitGroup v
      (idealPrimeExponent v.asIdeal (m F h12 x))) :
    lambda F h12 x v t = 1 := by
  exact RMKummerLeastLocalExponent.lambda_trivial_on_conductor_units F h12 x v t ht

theorem higher_units_zero (v : HeightOneSpectrum (𝓞 F)) :
    ClassFieldTheory.rayLocalHigherUnitGroup v 0 =
      (v.adicCompletionIntegers F).units := by
  exact RMKummerLeastLocalExponent.higherUnitGroup_zero F v

end
end DedekindZetaZeroFree.RMKummerCharacterAPI
