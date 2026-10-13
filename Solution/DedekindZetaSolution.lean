module

public import DedekindZetaZeroFree.HeckeCorollary

@[expose] public section

namespace DedekindZetaZeroFree

theorem main (K : Type) [Field K] [NumberField K] : ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
      ∀ s, 31 / 32 < s.re → s ≠ 1 → f s ≠ 0 := by
  exact DedekindZetaZeroFree.dedekindZeta_ne_zero K

theorem heckeCorollary
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (NumberField.RingOfIntegers K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (¬ χ.IsPrincipal → Differentiable ℂ f) ∧
      (∀ s, 1 < s.re → HasSum (fun I : Ideal (NumberField.RingOfIntegers K) =>
        χ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s)) ∧
      ∀ s, 31 / 32 < s.re → (s ≠ 1 ∨ ¬ χ.IsPrincipal) → f s ≠ 0 := by
  exact heckeL_ne_zero K m hm χ

end DedekindZetaZeroFree
