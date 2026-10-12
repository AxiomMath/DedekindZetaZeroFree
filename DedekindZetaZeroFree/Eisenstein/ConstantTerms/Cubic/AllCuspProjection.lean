module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Bruhat.TwoCellUnfolding

@[expose] public section

noncomputable section
open scoped NumberField Classical
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (f : ℂ → S) (hι : Function.Injective ι)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable (s : ℂ) (hs : s ∈ KPContActualChamberNormalSeries.V)
include hι hf hs

theorem actual_projected_upper_constantTerm_eq
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (t : ℝ) (b : KPCuspCharts.Shape F) :
    KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
      (fun ε => ∫ q : KPCompactFourier.AdditiveQuotient F,
        KPContActualChamberNormalSeries.E F ζ hζ U ι f s
          (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) *
            KPContFlatCuspIncomingEvaluation.localGroup F ζ hζ C R P H U a t 0 b ε)
        ∂KPWildKernelUpperBound.quotientHaar F) =
    KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s t •
      (KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s
        (by change -(1 : ℝ) / 6 < s.re; change (1 : ℝ) / 3 < s.re at hs; linarith)
        (f s)).val b +
    KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
      (fun ε => ∫ y : Adeles F,
        KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s)
          (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ y *
            KPContFlatCuspIncomingEvaluation.localGroup F ζ hζ C R P H U a t 0 b ε)
        ∂KPAdditiveHaar.adelicMeasure F) := by
  have hsΩ : s ∈ spectralDomain := by
    change -(1 : ℝ) / 6 < s.re
    change (1 : ℝ) / 3 < s.re at hs
    linarith
  have he : (fun ε => ∫ q : KPCompactFourier.AdditiveQuotient F,
      KPContActualChamberNormalSeries.E F ζ hζ U ι f s
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) *
          KPContFlatCuspIncomingEvaluation.localGroup F ζ hζ C R P H U a t 0 b ε)
      ∂KPWildKernelUpperBound.quotientHaar F) =
    (fun ε => KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s)
      (KPContFlatCuspIncomingEvaluation.localGroup F ζ hζ C R P H U a t 0 b ε)) +
    (fun ε => ∫ y : Adeles F,
      KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s)
        (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ y *
          KPContFlatCuspIncomingEvaluation.localGroup F ζ hζ C R P H U a t 0 b ε)
      ∂KPAdditiveHaar.adelicMeasure F) := by
    funext ε
    exact actual_upper_constantTerm_eq F ζ hζ U ι f hι hf s hs _
  rw [he, map_add]
  congr 1
  rw [← KPContFlatCuspIncomingEvaluation.incoming_formula F ζ hζ C R P H U a ι s hsΩ (f s) t b]
  unfold KPContFlatCuspIncomingEvaluation.W
  congr 1
  funext ε
  exact (KPContFlatCuspIncomingEvaluation.identitySheet_reindexed F ζ hζ C R P H U a ι s (f s) t 0 b ε).symm

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
