module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.CutoffGraphConvergence

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualGradientMeasure
open KPContActualCotangentMeasurableFamilies KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorQuotientRelationsComparison
set_option backward.isDefEq.respectTransparency true
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

theorem squareIntegral_original (v : Family (U := U) (H := H)) :
    (∫⁻ x, ENNReal.ofReal (normSquare v x : ℝ) ∂(baseMeasure (R := R) (P := P) (U := U))) =
    (∫⁻ x, ENNReal.ofReal (normSquare v (q F ζ hζ U (piTilde F ζ hζ U x)) : ℝ) ∂(R.quotientHaar)) := by
  have hm := (measurable_normSquare v).coe_nnreal_real.ennreal_ofReal
  change (∫⁻ x, ENNReal.ofReal (normSquare v x : ℝ) ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) = _
  rw [← map_q_coveredMeasure F ζ hζ R P U]
  rw [lintegral_map hm (q_continuous F ζ hζ U).measurable]
  rw [coveredMeasure]
  exact lintegral_map (hm.comp (q_continuous F ζ hζ U).measurable)
    (piTilde_continuous F ζ hζ U).measurable

theorem squareFinite_of_original_integrable (v : Family (U := U) (H := H))
    (hv : Integrable (fun x => (normSquare v (q F ζ hζ U (piTilde F ζ hζ U x)) : ℝ)) R.quotientHaar) :
    squareFinite (R := R) (P := P) v := by
  unfold squareFinite
  rw [squareIntegral_original F ζ hζ U R P H]
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => NNReal.coe_nonneg _)).mp hv.hasFiniteIntegral
end DedekindZetaZeroFree.FourierContinuation.ResidualGradientMeasure

end
