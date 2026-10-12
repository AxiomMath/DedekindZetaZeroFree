module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspGrowth.KernelTorusPeriodicity
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.CompactCrossRepresentatives

@[expose] public section

noncomputable section
open scoped Classical NumberField
set_option maxHeartbeats 1200000
namespace DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

theorem actualCuspSheet_global_exponential_bound
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
    (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ KPContActualChamberNormalSeries.V) :
    ∃ C₀ M : ℝ, 0 ≤ C₀ ∧ 0 ≤ M ∧
      ∀ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U,
        ∀ s ∈ K, ∀ xb : KPCuspCharts.Cross F, ∀ ε : rootsOfUnity 3 F, ∀ t : ℝ, 0 ≤ t →
          ‖KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s
            t xb.1 xb.2 ε‖ ≤ C₀ * Real.exp (M * t) := by
  have hF := (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).1
  have hrep : ∀ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U,
      ∃ B : Set (KPCuspCharts.Cross F), IsCompact B ∧ ∀ p : KPCuspCharts.Cross F,
        ∃ γ : KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U a,
          (KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U a).crossAction γ p ∈ B := by
    intro a
    exact compact_cross_representatives F hF _
      (KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U a)
      (KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U a)
  choose B hB hcover using hrep
  have hcompact : IsCompact (⋃ a, B a) := isCompact_iUnion hB
  obtain ⟨C₀, M, hC₀, hM, hbound⟩ := actualCuspSheet_exponential_bound
    F ζ hζ C R P H U ι hι f hf K hK hKV (⋃ a, B a) hcompact
  refine ⟨C₀, M, hC₀, hM, ?_⟩
  intro a s hs xb ε t ht
  obtain ⟨γ, hγ⟩ := hcover a xb
  have hh := hbound a s hs _ (Set.mem_iUnion.mpr ⟨a, hγ⟩) ε t ht
  rw [actualCuspSheet_norm_crossAction F ζ hζ C R P H U ι hι f hf a s (hKV hs)] at hh
  exact hh

end DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

end
