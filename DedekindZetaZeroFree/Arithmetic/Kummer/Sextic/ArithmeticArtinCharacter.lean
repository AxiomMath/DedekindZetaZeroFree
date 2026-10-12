module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.PrimitiveConductors.SexticSupport

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.PrimitiveRay
variable {F : Type} [Field F] [NumberField F]

def arithmeticSexticArtinCharacter (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (σ : F →+* ℂ) (u : Fˣ) : IdeleClassGroup F →ₜ* ℂˣ :=
  (sexticArtinCharacter ζ hζ σ u)⁻¹

@[simp] theorem arithmeticSexticArtinCharacter_apply
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (σ : F →+* ℂ)
    (u : Fˣ) (c : IdeleClassGroup F) :
    arithmeticSexticArtinCharacter ζ hζ σ u c =
      (sexticArtinCharacter ζ hζ σ u c)⁻¹ := rfl

theorem arithmeticSexticArtinCharacter_prime
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (σ : F →+* ℂ)
    (u : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (hSix : (Ideal.absNorm v.asIdeal).Coprime 6)
    (hu : v.valuation F (u : F) = 1) :
    ∃ j : Fin 6,
      v.valuation F ((u : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) -
        (ζ ^ 2) ^ j.val) < 1 ∧
      (arithmeticSexticArtinCharacter ζ hζ σ u
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
          (IdeleGroup.finitePrimeIdele v)) : ℂ) = σ ((ζ ^ 2) ^ j.val) := by
  obtain ⟨j, hj, he⟩ := sexticArtinCharacter_prime ζ hζ σ u v hSix hu
  refine ⟨j, hj, ?_⟩
  rw [arithmeticSexticArtinCharacter_apply, Units.val_inv_eq_inv_val, he, inv_inv]

theorem arithmeticSexticArtinCharacter_pow_six
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (σ : F →+* ℂ)
    (u : Fˣ) (c : IdeleClassGroup F) :
    arithmeticSexticArtinCharacter ζ hζ σ u c ^ 6 = 1 := by
  rw [arithmeticSexticArtinCharacter_apply, inv_pow,
    sexticArtinCharacter_pow_six, inv_one]

theorem arithmeticSexticArtinCharacter_unramified
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (σ : F →+* ℂ)
    (u : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (hSix : (Ideal.absNorm v.asIdeal).Coprime 6)
    (hu : v.valuation F (u : F) = 1)
    (t : (v.adicCompletion F)ˣ)
    (ht : t ∈ (v.adicCompletionIntegers F).units) :
    arithmeticSexticArtinCharacter ζ hζ σ u (IdeleGroup.finitePlaceIdeleClass v t) = 1 := by
  rw [arithmeticSexticArtinCharacter_apply,
    sexticArtinCharacter_unramified ζ hζ σ u v hSix hu t ht, inv_one]

theorem arithmeticSextic_primitiveRay_support
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (σ : F →+* ℂ)
    (u : Fˣ) (hc : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (χ : RayClassCharacter F m)
    (hprimitive : χ.IsPrimitive)
    (hχ : ∀ c : IdeleClassGroup F,
      RayClassBridge.ideleClassCharacter F hc m hm χ c =
        arithmeticSexticArtinCharacter ζ hζ σ u c)
    (v : HeightOneSpectrum (𝓞 F))
    (hSix : (Ideal.absNorm v.asIdeal).Coprime 6)
    (hu : v.valuation F (u : F) = 1) : ¬ m ≤ v.asIdeal := by
  exact primitiveRay_support hc (arithmeticSexticArtinCharacter ζ hζ σ u) m hm χ
    hprimitive hχ v (arithmeticSexticArtinCharacter_unramified ζ hζ σ u v hSix hu)

end DedekindZetaZeroFree.PrimitiveRay

end
