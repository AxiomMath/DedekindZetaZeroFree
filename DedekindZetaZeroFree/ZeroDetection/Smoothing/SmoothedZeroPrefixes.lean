module

public import DedekindZetaZeroFree.LFunctions.Hecke.EulerLogarithm
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.DyadicPrefixExtraction
public import DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.DyadicMassLowerBound

@[expose] public section

section

namespace DedekindZetaZeroFree.DetectorSmoothedZero

noncomputable section
open scoped NumberField

theorem zero_re_mem_Icc
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (ω : RayClassCharacter F 𝔪)
    (D : NonprincipalRayHeckeData F 𝔪 ω) (b β γ : ℝ) (hβ : b ≤ β)
    (hzero : D.L ((β : ℂ) + Complex.I * (γ : ℂ)) = 0) :
    β ∈ Set.Icc b 1 := by
  refine ⟨hβ, ?_⟩
  by_contra h
  have h : 1 < β := not_le.mp h
  have hs : 1 < ((β : ℂ) + Complex.I * (γ : ℂ)).re := by
    simpa using h
  have hne : D.L ((β : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 := by
    rw [← HeckeLogProof.ray_exp_eulerLog 𝔪 h𝔪 ω D _ hs]
    exact Complex.exp_ne_zero _
  exact hne hzero

end
end DedekindZetaZeroFree.DetectorSmoothedZero

end

section

namespace DedekindZetaZeroFree.DetectorSmoothedZero

noncomputable section
open scoped NumberField BigOperators Classical

theorem uniform_prefix_of_mass
    (F : Type) [Field F] [NumberField F] (C₀ ρ U₀ : ℝ) (hU₀ : 2 ≤ U₀)
    (hmass : ∀ U : ℝ, U₀ ≤ U →
      ∀ (𝔪 : Ideal (𝓞 F)), 𝔪 ≠ ⊥ →
        (Ideal.absNorm 𝔪 : ℝ) ≤ C₀ * U →
        ∀ ω : RayClassCharacter F 𝔪, ω.IsPrimitive → ¬ ω.IsPrincipal →
          ∀ D : NonprincipalRayHeckeData F 𝔪 ω,
            ∀ β γ : ℝ, β ∈ Set.Icc (249 / 250) 1 →
              |γ| ≤ 4 * U ^ ρ →
              D.L ((β : ℂ) + Complex.I * (γ : ℂ)) = 0 →
              (1 / 2 : ℝ) ≤
                ‖∑ n ∈ (Detector.ideals_bounded_norm_finite F
                    ((2 : ℝ) ^ detector_sz_dyadicUpper U)).toFinset.filter
                    (fun n => (2 : ℝ) ^ detector_sz_dyadicLower U <
                      (Ideal.absNorm n : ℝ)),
                  (Detector.truncatedIdealMoebius F U n : ℂ) * ω n *
                    (Ideal.absNorm n : ℂ) ^
                      (-(β : ℂ) - Complex.I * (γ : ℂ)) *
                    (Real.exp (-(Ideal.absNorm n : ℝ) / U ^ 10) : ℂ)‖) :
    ∀ U : ℝ, U₀ ≤ U →
      ∀ (𝔪 : Ideal (𝓞 F)), 𝔪 ≠ ⊥ →
      ∀ (ω : RayClassCharacter F 𝔪), ω.IsPrimitive → ¬ ω.IsPrincipal →
        (Ideal.absNorm 𝔪 : ℝ) ≤ C₀ * U →
        ∀ (D : NonprincipalRayHeckeData F 𝔪 ω) (β γ : ℝ),
          β ∈ Set.Icc (249 / 250) 1 → |γ| ≤ 4 * U ^ ρ →
          D.L ((β : ℂ) + Complex.I * (γ : ℂ)) = 0 →
          ∃ j ∈ detector_sz_dyadicIndices U,
            U ^ 2 / 2 < (2 : ℝ) ^ j ∧ (2 : ℝ) ^ j ≤ U ^ 11 ∧
            ∃ y ∈ Set.Icc ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)),
              (1 / 32 : ℝ) / (1 + Real.log U) ≤
                ‖∑ n ∈ (Detector.ideals_bounded_norm_finite F y).toFinset.filter
                    (fun n => (2 : ℝ) ^ j < (Ideal.absNorm n : ℝ)),
                  (Detector.truncatedIdealMoebius F U n : ℂ) * ω n *
                    (Ideal.absNorm n : ℂ) ^
                      (-(249 / 250 : ℂ) - Complex.I * (γ : ℂ))‖ := by
  intro U hU 𝔪 h𝔪 ω hωprim hωnp h𝔪norm D β γ hβ hγ hzero
  have hU2 : 2 ≤ U := le_trans hU₀ hU
  have hβle : (249 / 250 : ℝ) ≤ β := hβ.1
  obtain ⟨j, hj, y, hy, hle⟩ :=
    detector_sz_prefix_extraction F U β γ
      (fun n => (Detector.truncatedIdealMoebius F U n : ℂ) * ω n)
      hU2 hβle
      (hmass U hU 𝔪 h𝔪 h𝔪norm ω hωprim hωnp D β γ hβ hγ hzero)
  obtain ⟨hjlo, hjhi⟩ :=
    (detector_sz_dyadic_cover U hU2).2.2.2.2.2.1 j hj
  refine ⟨j, hj, hjlo, hjhi, y, hy, ?_⟩
  rwa [div_div]

end
end DedekindZetaZeroFree.DetectorSmoothedZero

end

section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField BigOperators Classical

theorem detector_smoothed_zero
    (F : Type) [Field F] [NumberField F]
    (htc : NumberField.IsTotallyComplex F) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    let A_F : ℝ := (detector_convexity_bridge F htc C₀ hC₀).choose
    ∀ ρ : ℝ, 0 < ρ → ρ < min (1 / 10) (1 / (A_F + 1)) →
      ∃ c : ℝ, 0 < c ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧
        ∀ U : ℝ, U₀ ≤ U →
        ∀ (𝔪 : Ideal (𝓞 F)), 𝔪 ≠ ⊥ →
        ∀ (ω : RayClassCharacter F 𝔪), ω.IsPrimitive → ¬ ω.IsPrincipal →
          (Ideal.absNorm 𝔪 : ℝ) ≤ C₀ * U →
          ∀ (D : NonprincipalRayHeckeData F 𝔪 ω) (β γ : ℝ),
            249 / 250 ≤ β → |γ| ≤ 4 * U ^ ρ →
            D.L ((β : ℂ) + Complex.I * (γ : ℂ)) = 0 →
            ∃ j ∈ detector_sz_dyadicIndices U,
              U ^ 2 / 2 < (2 : ℝ) ^ j ∧ (2 : ℝ) ^ j ≤ U ^ 11 ∧
              ∃ y ∈ Set.Icc ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)),
                c / (1 + Real.log U) ≤
                  ‖∑ n ∈ (Detector.ideals_bounded_norm_finite F y).toFinset.filter
                      (fun n => (2 : ℝ) ^ j < (Ideal.absNorm n : ℝ)),
                    (Detector.truncatedIdealMoebius F U n : ℂ) * ω n *
                      (Ideal.absNorm n : ℂ) ^
                        (-(249 / 250 : ℂ) - Complex.I * (γ : ℂ))‖ := by
  dsimp only
  intro ρ hρ hρhi
  obtain ⟨U₀, hU₀, hmass⟩ :=
    detector_sz_dyadic_mass_at_bridge F htc C₀ hC₀ ρ hρ hρhi
  refine ⟨1 / 32, by norm_num, U₀, hU₀, ?_⟩
  intro U hU 𝔪 h𝔪 ω hprim hn hnorm D β γ hβ hγ hzero
  exact DetectorSmoothedZero.uniform_prefix_of_mass F C₀ ρ U₀ hU₀ hmass
    U hU 𝔪 h𝔪 ω hprim hn hnorm D β γ
    (DetectorSmoothedZero.zero_re_mem_Icc F 𝔪 h𝔪 ω D _ β γ hβ hzero)
    hγ hzero

end
end DedekindZetaZeroFree

end
