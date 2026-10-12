module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.ConductorFrobeniusAgreement
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.ProductConductorComparison

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.RootNumber

open scoped NumberField Classical
open IsDedekindDomain

theorem primitive_conductor_lower
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hn : ¬η.IsPrincipal) (hp : η.IsPrimitive)
    (d : QuadraticRayExtensionData η)
    (c : ClassFieldTheory.RayClassModulus F)
    (hc : ClassFieldTheory.IsAbelianConductor F d.extension c) :
    f ∣ finiteModulusIdeal c := by
  obtain ⟨θ, hθ⟩ :=
    conductor_character F hF f hf η hq hn d c hc
  refine DedekindZetaZeroFree.LargeSieve.RayComparison.primitive_conductor_dvd (m := f)
    (f := finiteModulusIdeal c) (q := ⊤) hf (finiteModulusIdeal_ne_bot c) (by simp)
    η θ hp ?_
  intro I hI hcop
  exact conductor_frobenius_agreement F hF f hf η hq hn d c hc θ hθ I hI
    (by simpa only [Ideal.mul_top] using hcop)

theorem primitive_conductor_support_lower
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hn : ¬η.IsPrincipal) (hp : η.IsPrimitive)
    (d : QuadraticRayExtensionData η)
    (c : ClassFieldTheory.RayClassModulus F)
    (hc : ClassFieldTheory.IsAbelianConductor F d.extension c) :
    ∀ p : HeightOneSpectrum (𝓞 F),
      p.asIdeal ⊔ f ≠ ⊤ → p ∈ c.finitePart.support := by
  have hdvd : f ∣ finiteModulusIdeal c :=
    primitive_conductor_lower F hF f hf η hq hn hp d c hc
  have hle : finiteModulusIdeal c ≤ f := Ideal.dvd_iff_le.mp hdvd
  intro p hp
  rw [mem_finitePart_support_iff]
  intro hcontra
  exact hp (le_antisymm le_top (hcontra ▸ sup_le_sup_left hle p.asIdeal))

end DedekindZetaZeroFree.LargeSieve.RootNumber
