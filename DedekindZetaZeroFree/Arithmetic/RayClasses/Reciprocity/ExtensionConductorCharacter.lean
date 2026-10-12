module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.FiniteModulusIdeal
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.QuadraticExtensionRealization
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.ArtinMapAtContainingModulus
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.IdealCharacterFromGroup

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.RootNumber

open scoped NumberField Classical
open IsDedekindDomain

theorem conductor_character
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hn : ¬η.IsPrincipal) (d : QuadraticRayExtensionData η)
    (c : ClassFieldTheory.RayClassModulus F)
    (hc : ClassFieldTheory.IsAbelianConductor F d.extension c) :
    let g := finiteModulusIdeal c
    ∃ θ : DedekindZetaZeroFree.RayClassCharacter F g,
      ∀ p : HeightOneSpectrum (𝓞 F), p.asIdeal ⊔ g = ⊤ →
        ∀ Q : HeightOneSpectrum (𝓞 d.extension),
          Q.asIdeal.LiesOver p.asIdeal →
            θ p.asIdeal =
              (d.character (ClassFieldTheory.arithmeticFrobeniusAt (K := F) Q) : ℂ) := by
  dsimp only
  have hemb : ClassFieldTheory.EmbedsInRayClassField F d.extension
      (DedekindZetaZeroFree.LargeSieve.RayBridge.fullModulus (finiteModulusIdeal c)
        (finiteModulusIdeal_ne_bot c)) := by
    rw [fullModulus_finiteModulusIdeal hF c]
    exact (hc c).mpr le_rfl
  obtain ⟨A, -, hA⟩ := artin_at_containing_modulus d.extension
    (DedekindZetaZeroFree.LargeSieve.RayBridge.fullModulus (finiteModulusIdeal c)
      (finiteModulusIdeal_ne_bot c)) hemb
  refine ⟨RayBridge.characterFromRayGroup (finiteModulusIdeal c)
    (finiteModulusIdeal_ne_bot c) (d.character.comp A), ?_⟩
  intro p hcop Q hQ
  rw [RayBridge.characterFromRayGroup_apply (finiteModulusIdeal c)
        (finiteModulusIdeal_ne_bot c) (d.character.comp A) p.asIdeal p.ne_bot hcop,
      RayBridge.idealClass_prime (finiteModulusIdeal c)
        (finiteModulusIdeal_ne_bot c) p hcop]
  simp only [MonoidHom.comp_apply]
  rw [hA p (RayBridge.prime_not_mem_fullModulus_support (finiteModulusIdeal c)
        (finiteModulusIdeal_ne_bot c) p hcop) Q hQ]

end DedekindZetaZeroFree.LargeSieve.RootNumber
