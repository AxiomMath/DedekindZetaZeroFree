module

public import DedekindZetaZeroFree.LFunctions.Hecke.FunctionalEquation.Nonprincipal
public import DedekindZetaZeroFree.LFunctions.Hecke.FunctionalEquation.Principal

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

open scoped NumberField Classical

theorem heckeFunctionalEquation :
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyComplex F →
  ∀ (𝔪 : Ideal (𝓞 F)), 𝔪 ≠ ⊥ → ∀ η : DedekindZetaZeroFree.RayClassCharacter F 𝔪, η.IsPrimitive →
    (¬ η.IsPrincipal → ∃ (Λ Λ' : ℂ → ℂ) (W : ℂ), Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧ ‖W‖ = 1 ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun I : Ideal (𝓞 F) =>
        (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm 𝔪 : ℂ)) ^ (s / 2) *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F *
          (η I * (Ideal.absNorm I : ℂ) ^ (-s))) (Λ s)) ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun I : Ideal (𝓞 F) =>
        (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm 𝔪 : ℂ)) ^ (s / 2) *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F *
          ((starRingEnd ℂ) (η I) * (Ideal.absNorm I : ℂ) ^ (-s))) (Λ' s)) ∧
      (∀ s : ℂ, Λ s = W * Λ' (1 - s)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ, ‖Λ s‖ ≤ C * Real.exp (‖s‖ ^ (1 + ε)))) ∧
    (η.IsPrincipal → ∃ (Λ E : ℂ → ℂ), DifferentiableOn ℂ Λ {s | s ≠ 0 ∧ s ≠ 1} ∧
      Differentiable ℂ E ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun I : Ideal (𝓞 F) =>
        (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm 𝔪 : ℂ)) ^ (s / 2) *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F *
          (η I * (Ideal.absNorm I : ℂ) ^ (-s))) (Λ s)) ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ s = Λ (1 - s)) ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → E s = s * (s - 1) * Λ s) ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ, ‖E s‖ ≤ C * Real.exp (‖s‖ ^ (1 + ε)))) := by
  intro F _ _ hF m hm η hprim
  exact ⟨fun hnonprincipal =>
      heckeNonprincipalFunctionalEquation F hF m hm η hprim hnonprincipal,
    fun hprincipal =>
      heckeFunctionalEquation_principal F hF m hm η hprim hprincipal⟩

end DedekindZetaZeroFree.Hecke
