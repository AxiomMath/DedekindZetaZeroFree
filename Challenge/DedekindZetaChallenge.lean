module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical

structure RayClassCharacter (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) where
  toFun : Ideal (𝓞 F) → ℂ
  map_mul' : ∀ I J, toFun (I * J) = toFun I * toFun J
  map_top' : toFun ⊤ = 1
  eq_zero_iff' : ∀ I, toFun I = 0 ↔ (I = ⊥ ∨ I ⊔ 𝔪 ≠ ⊤)
  map_span' : ∀ α : 𝓞 F, α ≠ 0 → α - 1 ∈ 𝔪 → (∀ φ : F →+* ℝ, 0 < φ (α : F)) →
    toFun (Ideal.span {α}) = 1

instance (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) :
    CoeFun (RayClassCharacter F 𝔪) (fun _ => Ideal (𝓞 F) → ℂ) :=
  ⟨RayClassCharacter.toFun⟩

def RayClassCharacter.IsPrincipal {F : Type} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
    (η : RayClassCharacter F 𝔪) : Prop :=
  ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ 𝔪 = ⊤ → η I = 1

theorem main (K : Type) [Field K] [NumberField K] : ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
      ∀ s, 31 / 32 < s.re → s ≠ 1 → f s ≠ 0 := by sorry

theorem heckeCorollary
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (NumberField.RingOfIntegers K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (¬ χ.IsPrincipal → Differentiable ℂ f) ∧
      (∀ s, 1 < s.re → HasSum (fun I : Ideal (NumberField.RingOfIntegers K) =>
        χ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s)) ∧
      ∀ s, 31 / 32 < s.re → (s ≠ 1 ∨ ¬ χ.IsPrincipal) → f s ≠ 0 := by sorry

end

end DedekindZetaZeroFree
