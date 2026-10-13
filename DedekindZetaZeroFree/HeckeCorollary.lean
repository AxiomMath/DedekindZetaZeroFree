module

public import DedekindZetaZeroFree.Nonvanishing.Hecke.NonprincipalCharacter
public import DedekindZetaZeroFree.Nonvanishing.Hecke.PrincipalCharacter

@[expose] public section

namespace DedekindZetaZeroFree

open scoped NumberField

theorem heckeL_ne_zero
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (¬ χ.IsPrincipal → Differentiable ℂ f) ∧
      (∀ s, 1 < s.re → HasSum (fun I : Ideal (𝓞 K) =>
        χ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s)) ∧
      ∀ s, 31 / 32 < s.re → (s ≠ 1 ∨ ¬ χ.IsPrincipal) → f s ≠ 0 := by
  by_cases hχ : χ.IsPrincipal
  · obtain ⟨f, hf, hsum, hnz⟩ := HeckeCorollary.principalRayCharacter_ne_zero K m hm χ hχ
    refine ⟨f, hf, fun h => (h hχ).elim, hsum, ?_⟩
    intro s hs hregular
    exact hnz s hs (hregular.resolve_right (not_not.mpr hχ))
  · obtain ⟨f, hf, hsum, hnz⟩ := HeckeCorollary.nonprincipalRayCharacter_ne_zero K m hm χ hχ
    exact ⟨f, hf.differentiableOn, fun _ => hf, hsum, fun s hs _ => hnz s hs⟩

end DedekindZetaZeroFree
