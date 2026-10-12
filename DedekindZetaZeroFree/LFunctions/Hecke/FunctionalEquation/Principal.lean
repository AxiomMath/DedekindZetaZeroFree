module

public import DedekindZetaZeroFree.LFunctions.Hecke.Growth.PoleClearedOrderOne
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalCompletedIdealSeries
public import DedekindZetaZeroFree.Theta.Profiles.MixedPairExponentialTails
public import DedekindZetaZeroFree.Theta.Inversion.MixedPairGlobalSelfDuality

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

open scoped NumberField

theorem heckeFunctionalEquation_principal
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (hη : η.IsPrimitive) (hprincipal : η.IsPrincipal) :
    ∃ (Λ E : ℂ → ℂ), DifferentiableOn ℂ Λ {s | s ≠ 0 ∧ s ≠ 1} ∧
      Differentiable ℂ E ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun I : Ideal (𝓞 F) =>
        (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F *
          (η I * (Ideal.absNorm I : ℂ) ^ (-s))) (Λ s)) ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ s = Λ (1 - s)) ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → E s = s * (s - 1) * Λ s) ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ,
        ‖E s‖ ≤ C * Real.exp (‖s‖ ^ (1 + ε))) := by
  classical
  set P := DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F with hP
  have hk : P.k = 1 := rfl
  refine ⟨P.Λ, poleCleared P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact weakFEPair_differentiableOn_weightOne P hk
  · exact poleCleared_differentiable P hk
  · intro s hs
    exact principal_prefactor_all_ideal_hasSum F hF m η hη hprincipal s hs
  · intro s hs0 hs1
    exact weakFEPair_selfDual_reflection P hk (mixedThetaPair_global_selfDual F)
      (mixedThetaPair_global_g₀_eq_f₀ F) (mixedThetaPair_global_ε_eq_one F) s hs0 hs1
  · intro s hs0 hs1
    exact poleCleared_eq P hk s hs0 hs1
  · intro ε hε
    obtain ⟨hp, A, B, hA, hB, htail⟩ := mixedThetaPair_exponential_tail F
    refine WeakFEPair.orderOneBound_poleClear P hk
      ⟨A, B, 2 / (Module.finrank ℚ F : ℝ), hA.le, hB, hp, ?_⟩
      (poleCleared P) (fun s => rfl) ε hε
    intro t ht
    exact htail t ht

end DedekindZetaZeroFree.Hecke
