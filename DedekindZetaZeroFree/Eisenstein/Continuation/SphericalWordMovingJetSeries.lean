module

public import DedekindZetaZeroFree.Analysis.SmoothFunctions.MovingJetTaylorSeries
public import DedekindZetaZeroFree.Eisenstein.Continuation.SphericalWordCoherentNumerator

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff BigOperators
namespace DedekindZetaZeroFree.SharedSource
open KPGlobalResidualConstruction KPGlobalEisensteinData KPContActualSphericalRightFieldIdentification
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

include C R P H in

theorem sphericalWord_moving_series
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (w : List (Fin (groupDimension F))) :
    ∃ A : ℂ → KPLiteralRaw.Functions F ζ hζ,
      (∀ s, (1 / 3 : ℝ) < s.re → ∀ g,
        A s g = actualRightWord F ζ hζ w
          (fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
              (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out c) * h)) g) ∧
      (∀ g, MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (0 : ℂ) ρ ⊆ KPContinuation.spectralDomain ∧
        ∃ N : ℂ → nativeSmoothSpace F ζ hζ,
          (∀ s ∈ Metric.ball (0 : ℂ) ρ, s ≠ 0 → (N s).val = s • A s) ∧
          (∀ g, AnalyticOnNhd ℂ (fun s => (N s).val g) (Metric.ball (0 : ℂ) ρ)) ∧
          ∃ b : ℕ → nativeSmoothSpace F ζ hζ,
            SmoothPowerSeriesOn (movingJetMap F ζ hζ) 0 ρ b N := by
  obtain ⟨A, N, hch, hm, ρ, hρ, hb, he, ha, hs, b, hbs, ht⟩ :=
    sphericalWord_coherent_numerator F ζ hζ C R P H U v w
  let NN : ℂ → nativeSmoothSpace F ζ hζ := fun s => ⟨N s, hs s⟩
  let bb : ℕ → nativeSmoothSpace F ζ hζ := fun n => ⟨b n, hbs n⟩
  exact ⟨A, hch, hm, ρ, hρ, hb, NN, he, ha, bb,
    movingJet_powerSeries_of_compact_taylor F ζ hζ bb NN ρ hρ ht⟩

end DedekindZetaZeroFree.SharedSource

end
