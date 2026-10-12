module

public import DedekindZetaZeroFree.Arithmetic.Kummer.FrequencyClassesAndCharacterRigidity

@[expose] public section

open scoped NumberField
open IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.Detector.Conductor.Raw
noncomputable section

def frequencySInteger (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (U : FrequencyRepresentatives F S)
    (u : U.carrier) : S.integer F :=
  ⟨(u.val : F), (U.power_free u.val u.property).1⟩

def frequencyRadicalSNorm (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (U : FrequencyRepresentatives F S)
    (u : U.carrier) : ℕ :=
  Nat.card ((S.integer F) ⧸ (Ideal.span {frequencySInteger F S U u}).radical)

def idealAwayPrimePart (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  ((normalizedFactors I).filter (fun p => p ≠ v.asIdeal)).prod

def integralElementLocalUnit (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) (ha : a ≠ 0) : (v.adicCompletion F)ˣ :=
  Units.mk0 (NumberField.FinitePlace.embedding v (a : F))
    ((NumberField.FinitePlace.embedding v).injective.ne
      (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ha))

def IsFrequencyLocalComponent (F : Type) [Field F] [NumberField F]
    (χ : PrimitiveFrequencyCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (δ : (v.adicCompletion F)ˣ →ₜ* ℂˣ) : Prop :=
  ∀ (a : 𝓞 F) (ha : a ≠ 0), a - 1 ∈ idealAwayPrimePart F v χ.conductor →
    (δ (integralElementLocalUnit F v a ha) : ℂ) =
      (χ.character (idealAwayPrimePart F v (Ideal.span {a})))⁻¹

end
end DedekindZetaZeroFree.Detector.Conductor.Raw
