module

public import DedekindZetaZeroFree.Theta.RayClasses.PrimitiveNonprincipalThetaPair
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.StrongPairContinuation
public import DedekindZetaZeroFree.LFunctions.Hecke.Growth.NormalizedCompletionOrderOne

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

open scoped NumberField

theorem heckeNonprincipalFunctionalEquation
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (hprim : η.IsPrimitive) (hnonprincipal : ¬ η.IsPrincipal) :
    ∃ (Λ Λ' : ℂ → ℂ) (W : ℂ),
      Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧ ‖W‖ = 1 ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun I : Ideal (𝓞 F) =>
        (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F *
          (η I * (Ideal.absNorm I : ℂ) ^ (-s))) (Λ s)) ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun I : Ideal (𝓞 F) =>
        (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F *
          ((starRingEnd ℂ) (η I) * (Ideal.absNorm I : ℂ) ^ (-s))) (Λ' s)) ∧
      (∀ s : ℂ, Λ s = W * Λ' (1 - s)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ,
        ‖Λ s‖ ≤ C * Real.exp (‖s‖ ^ (1 + ε))) := by
  obtain ⟨P, hk, hf₀, hg₀, hε, _hf, _hg, _hconj, hdecay, hseries⟩ :=
    primitiveNonprincipalThetaPair F hF m hm η hprim hnonprincipal
  have hP : IsStrongFEPair P := ⟨hf₀, hg₀⟩
  obtain ⟨hΛ, hΛ', hMf, hMg, hFE⟩ := mellinStrongPairContinuation P hk hP
  refine ⟨P.Λ, P.symm.Λ, P.ε, hΛ, hΛ', hε, ?_, ?_, hFE, ?_⟩
  · intro s hs
    have hsum := (hseries s hs).2.2.1
    rw [(hMf s).2] at hsum
    exact hsum
  · intro s hs
    have hsum := (hseries s hs).2.2.2
    rw [(hMg s).2] at hsum
    exact hsum
  · apply strongPair_orderOneBound P hk hP
    obtain ⟨C, b, p, hC, hb, hp, htail⟩ := hdecay
    refine ⟨C, b, p, hC.le, hb, hp, ?_⟩
    intro t ht
    simpa [hf₀, hg₀, Real.rpow_eq_pow] using htail t ht

end DedekindZetaZeroFree.Hecke
