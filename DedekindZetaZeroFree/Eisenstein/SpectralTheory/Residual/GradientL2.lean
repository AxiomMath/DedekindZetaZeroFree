module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.GradientSquareIntegrability
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.SectionGradientAndEnergy

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualGradientL2
open KPContSectorSmoothFramesSupport KPContActualSectorCutoffGraphLimit
open ResidualSphericalGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

theorem squareFinite_of_first_derivatives (Z : smoothSections F ζ hζ U R P H)
    (h2 : ∀ b : KPSmoothActualFlowData.B F,
      MemLp (KPSmoothActualFlowData.flowDerivative F ζ hζ b
        (originalScalar F ζ hζ U R P H Z)) 2 R.quotientHaar) :
    KPContActualCotangentMeasurableFamilies.squareFinite (R := R) (P := P) (gradient Z) := by
  let f := originalScalar F ζ hζ U R P H Z
  let E := fun x => ∑ w : NumberField.InfinitePlace F,
    ((‖KPSmoothActualFlowData.flowDerivative F ζ hζ (w,0) f x‖^2 +
      ‖KPSmoothActualFlowData.flowDerivative F ζ hζ (w,1) f x‖^2)/4 +
    (‖KPSmoothActualFlowData.flowDerivative F ζ hζ (w,2) f x‖^2 +
      ‖KPSmoothActualFlowData.flowDerivative F ζ hζ (w,3) f x‖^2 +
      ‖KPSmoothActualFlowData.flowDerivative F ζ hζ (w,4) f x‖^2 +
      ‖KPSmoothActualFlowData.flowDerivative F ζ hζ (w,5) f x‖^2)/2)
  have hi (b) : Integrable (fun x => ‖KPSmoothActualFlowData.flowDerivative F ζ hζ b f x‖^2)
      R.quotientHaar := (memLp_two_iff_integrable_sq_norm (h2 b).aestronglyMeasurable).mp (h2 b)
  have hE : Integrable E R.quotientHaar := by
    apply integrable_finset_sum
    intro w _
    exact (((hi (w,0)).add (hi (w,1))).div_const 4).add
      (((((hi (w,2)).add (hi (w,3))).add (hi (w,4))).add (hi (w,5))).div_const 2)
  apply ResidualGradientMeasure.squareFinite_of_original_integrable F ζ hζ U R P H
  apply hE.congr
  filter_upwards [] with x
  induction x using Quotient.inductionOn with
  | h g =>
    exact (ResidualSectionGradient.gradient_norm_original F ζ hζ U R P H Z g).symm
end DedekindZetaZeroFree.FourierContinuation.ResidualGradientL2

end
