module

public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.LogJetTransport

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling
open MeasureTheory KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open KPCplxRotatedKernelEstimates KPCplxRotatedRapidDecay ThetaArchInducedMajorant
open ThetaRawSheetEnvelope.WeightedWhittakerSheets
open scoped Classical Topology ENNReal

def standardComplexParameter : ℂˣ :=
  Units.mk0 ((4 * Real.pi : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (by positivity))

@[simp] lemma standardComplexParameter_scale :
    characterScale standardComplexParameter = 4 * Real.pi := by
  simp [standardComplexParameter, characterScale, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (show 0 < 4 * Real.pi by positivity)]

def standardWeylJacquet (κ : ℂˣ) (f : PrincipalSeries positiveParameter)
    (y : ℂˣ) : ℂ :=
  (κ : ℂ) * KPCplxJacquetFunctional.jacquetIntegral standardComplexParameter
    (KPCplxPrincipalSeriesCharts.pi positiveParameter (Matrix.ProjGenLinGroup.mk (diagonal y * weyl)) f)

end DedekindZetaZeroFree.SheetRescaling

end
