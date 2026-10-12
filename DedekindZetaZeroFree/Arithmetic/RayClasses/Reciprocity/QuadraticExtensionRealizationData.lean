module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt

@[expose] public section

open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.LargeSieve

structure QuadraticRayExtensionData
    {F : Type} [Field F] [NumberField F] {f : Ideal (𝓞 F)}
    (η : DedekindZetaZeroFree.RayClassCharacter F f) where
  extension : ClassFieldTheory.FiniteAbelianExtension F
  character : (extension ≃ₐ[F] extension) →* ℂˣ
  degree_two : Module.finrank F extension = 2
  character_injective : Function.Injective character
  character_square : ∀ σ, character σ ^ 2 = 1
  unramified : ∀ p : HeightOneSpectrum (𝓞 F),
    p.asIdeal ⊔ f = ⊤ → Algebra.IsUnramifiedIn (𝓞 extension) p.asIdeal
  frobenius : ∀ (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal ⊔ f = ⊤)
    (Q : HeightOneSpectrum (𝓞 extension)), Q.asIdeal.LiesOver p.asIdeal →
      (character (ClassFieldTheory.arithmeticFrobeniusAt (K := F) Q) : ℂ) =
        η p.asIdeal

end DedekindZetaZeroFree.LargeSieve
