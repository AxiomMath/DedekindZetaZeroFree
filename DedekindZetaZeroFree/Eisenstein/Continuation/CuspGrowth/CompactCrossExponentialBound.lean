module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspGrowth.RationalSeriesExponentialBound
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.CasimirParameterJets

@[expose] public section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

theorem actualCuspSheet_exponential_bound
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (hι : Function.Injective ι) (f : ℂ → S)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ KPContActualChamberNormalSeries.V)
    (B : Set (KPCuspCharts.Cross F)) (hB : IsCompact B) :
    ∃ C₀ M : ℝ, 0 ≤ C₀ ∧ 0 ≤ M ∧
      ∀ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U,
        ∀ s ∈ K, ∀ xb ∈ B, ∀ ε : rootsOfUnity 3 F, ∀ t : ℝ, 0 ≤ t →
          ‖KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s
            t xb.1 xb.2 ε‖ ≤ C₀ * Real.exp (M * t) := by
  let D : Set (KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ) :=
    Set.range (fun aε : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U ×
      rootsOfUnity 3 F =>
      KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U aε.1 aε.2)
  have hD : IsCompact D := (Set.finite_range _).isCompact
  obtain ⟨C₀, M, hC₀, hM, hbound⟩ :=
    actualSeries_exponential_bound F ζ hζ U ι f hf K hK hKV B hB D hD
  refine ⟨C₀, M, hC₀, hM, ?_⟩
  intro a s hs xb hxb ε t ht
  simp only [KPContActualChamberCasimirJets.cuspSheet,
    KPContActualChamberCasimirJets.jet, iteratedDerivWithin_zero,
    KPContFlatCuspIncomingEvaluation.cuspGroup]
  rw [(KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s (hKV hs)).1]
  exact hbound s hs xb hxb _ ⟨(a, ε), rfl⟩ t ht

end DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

end
