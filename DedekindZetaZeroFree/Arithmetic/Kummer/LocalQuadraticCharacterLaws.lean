module

public import DedekindZetaZeroFree.Arithmetic.Kummer.LocalHilbertSymbolComparison

@[expose] public section

namespace DedekindZetaZeroFree.RMKummerLocalSquareLaws

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

theorem lambda_mul (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x y : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    RMKummerLocalNormCharacter.lambda F h12 (x * y) v t =
      RMKummerLocalNormCharacter.lambda F h12 x v t *
        RMKummerLocalNormCharacter.lambda F h12 y v t := by
  letI : ValuativeRel (v.adicCompletion F) :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel F v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v
  rw [RMKummerLocalHilbertComparison.lambda_eq_inverse_localHilbertSymbol,
    RMKummerLocalHilbertComparison.lambda_eq_inverse_localHilbertSymbol,
    RMKummerLocalHilbertComparison.lambda_eq_inverse_localHilbertSymbol, map_mul]
  erw [ClassFieldTheory.localHilbertSymbol_mul_right, map_mul, mul_inv_rev]
  exact mul_comm _ _

private theorem lambda_at_one (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    RMKummerLocalNormCharacter.lambda F h12 1 v t = 1 := by
  have h := lambda_mul F h12 1 1 v t
  simp only [one_mul] at h
  exact mul_eq_left.mp h.symm

private theorem lambda_square (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    RMKummerLocalNormCharacter.lambda F h12 x v t ^ 2 = 1 := by
  letI : ValuativeRel (v.adicCompletion F) :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel F v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v
  rw [RMKummerLocalHilbertComparison.lambda_eq_inverse_localHilbertSymbol, inv_pow]
  erw [rmKummerQuadraticRootsComplexMap_pow_two, inv_one]

theorem lambda_div (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x y : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    RMKummerLocalNormCharacter.lambda F h12 (x / y) v t =
      RMKummerLocalNormCharacter.lambda F h12 x v t *
        (RMKummerLocalNormCharacter.lambda F h12 y v t)⁻¹ := by
  have h := lambda_mul F h12 (x / y) y v t
  have h' := congrArg (fun z : Fˣ => RMKummerLocalNormCharacter.lambda F h12 z v t)
    (div_mul_cancel x y)
  with_reducible exact eq_mul_inv_of_mul_eq (h.symm.trans h')

theorem lambda_mul_sq (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x y : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    RMKummerLocalNormCharacter.lambda F h12 (x * y ^ 2) v t =
      RMKummerLocalNormCharacter.lambda F h12 x v t := by
  rw [lambda_mul, pow_two, lambda_mul, ← pow_two, lambda_square, mul_one]

theorem lambda_one (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    RMKummerLocalNormCharacter.lambda F h12 1 v t = 1 := by
  exact lambda_at_one F h12 v t

theorem lambda_eq_one_or_neg_one (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    RMKummerLocalNormCharacter.lambda F h12 x v t = 1 ∨
      RMKummerLocalNormCharacter.lambda F h12 x v t = -1 := by
  have h : (RMKummerLocalNormCharacter.lambda F h12 x v t : ℂ) ^ 2 = 1 := by
    exact congrArg (fun z : ℂˣ => (z : ℂ)) (lambda_square F h12 x v t)
  rcases sq_eq_one_iff.mp h with h | h
  · left; exact Units.ext h
  · right; exact Units.ext h

theorem lambda_inv_eq_conj (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    (((RMKummerLocalNormCharacter.lambda F h12 x v t)⁻¹ : ℂˣ) : ℂ) =
      star (RMKummerLocalNormCharacter.lambda F h12 x v t : ℂ) := by
  rcases lambda_eq_one_or_neg_one F h12 x v t with h | h <;>
    simp [h]

end
end DedekindZetaZeroFree.RMKummerLocalSquareLaws
