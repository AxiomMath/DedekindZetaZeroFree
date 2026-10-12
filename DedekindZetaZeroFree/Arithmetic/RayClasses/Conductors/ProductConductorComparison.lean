module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterUniqueness
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveModulusComparison

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.RayComparison

open scoped NumberField Classical
open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]

theorem away_uniqueness {m q : Ideal (𝓞 F)}
    (hm : m ≠ ⊥) (hq : q ≠ ⊥)
    (η θ : RayClassCharacter F m)
    (hagree : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ (m * q) = ⊤ → η I = θ I) :
    ∀ I : Ideal (𝓞 F), η I = θ I :=
  DedekindZetaZeroFree.LargeSieve.rayCharacter_eq_of_eq_away hm hq η θ hagree

theorem primitive_conductor_dvd {m f q : Ideal (𝓞 F)}
    (hm : m ≠ ⊥) (hf : f ≠ ⊥) (hq : q ≠ ⊥)
    (η : RayClassCharacter F m) (θ : RayClassCharacter F f)
    (hprim : η.IsPrimitive)
    (hagree : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ (m * f * q) = ⊤ → η I = θ I) :
    m ∣ f :=
  Ideal.dvd_iff_le.mpr
    (DedekindZetaZeroFree.LargeSieve.rayCharacter_primitive_modulus_le hm hf hq η hprim θ hagree)

theorem primitive_product_conductor_dvd {m f k q : Ideal (𝓞 F)}
    (hm : m ≠ ⊥) (hf : f ≠ ⊥) (hk : k ≠ ⊥) (hq : q ≠ ⊥)
    (η : RayClassCharacter F m) (θ : RayClassCharacter F f)
    (ξ : RayClassCharacter F k) (hprim : η.IsPrimitive)
    (hagree : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ (m * f * k * q) = ⊤ →
      η I = θ I * ξ I) :
    m ∣ f * k := by
  have hfk : f * k ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim hf hk
  refine Ideal.dvd_iff_le.mpr
    (DedekindZetaZeroFree.LargeSieve.rayCharacter_primitive_modulus_le hm hfk hq η hprim
      (DedekindZetaZeroFree.LargeSieve.RayOperations.mul θ ξ) ?_)
  intro I hI hcop
  rw [DedekindZetaZeroFree.LargeSieve.RayOperations.mul_apply]
  refine hagree I hI ?_
  simpa only [mul_assoc] using hcop

end DedekindZetaZeroFree.LargeSieve.RayComparison
