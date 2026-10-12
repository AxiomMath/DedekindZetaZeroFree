module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.ProductConductorComparison
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.IdealCharacterFromGroup

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem initial_ray_principal_descent_equiv {F : Type} [Field F] [NumberField F]
    {m f : Ideal (𝓞 F)} (hm : m ≠ ⊥) (hf : f ≠ ⊥) (hfm : f ∣ m)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (θ : DedekindZetaZeroFree.RayClassCharacter F f)
    (hind : ∀ I : Ideal (𝓞 F),
      η I = if I = ⊥ ∨ I ⊔ m ≠ ⊤ then 0 else θ I) :
    η.IsPrincipal ↔ θ.IsPrincipal := by

  have hmf : m ≤ f := Ideal.dvd_iff_le.mp hfm

  have hηθ : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ m = ⊤ → η I = θ I := by
    intro I hI hIcop
    have hcond : ¬ (I = ⊥ ∨ I ⊔ m ≠ ⊤) := by
      rintro (h | h)
      · exact hI h
      · exact h hIcop
    rw [hind I]
    simp only [hcond, ↓reduceIte]
  constructor
  ·
    intro hη

    let ε : DedekindZetaZeroFree.RayClassCharacter F f :=
      RayBridge.characterFromRayGroup f hf
        (1 : ClassFieldTheory.RayClassGroup (RayBridge.fullModulus f hf) →* ℂˣ)
    have hεprincipal : ε.IsPrincipal := by
      intro I hI hIf
      rw [RayBridge.characterFromRayGroup_apply f hf _ I hI hIf]
      simp

    have hθε : ∀ I : Ideal (𝓞 F), θ I = ε I :=
      RayComparison.away_uniqueness hf hm θ ε (by
        intro I hI hIfm
        have hIf : I ⊔ f = ⊤ :=
          top_unique (le_trans (le_of_eq hIfm.symm) (sup_le_sup_left Ideal.mul_le_left I))
        have hIm : I ⊔ m = ⊤ :=
          top_unique (le_trans (le_of_eq hIfm.symm) (sup_le_sup_left Ideal.mul_le_right I))
        have h1 : θ I = 1 := by rw [← hηθ I hI hIm, hη I hI hIm]
        exact h1.trans (hεprincipal I hI hIf).symm)
    intro I hI hIf
    rw [hθε I, hεprincipal I hI hIf]
  ·
    intro hθ I hI hIm
    have hIf : I ⊔ f = ⊤ :=
      top_unique (le_trans (le_of_eq hIm.symm) (sup_le_sup_left hmf I))
    rw [hηθ I hI hIm]
    exact hθ I hI hIf

end DedekindZetaZeroFree.LargeSieve
