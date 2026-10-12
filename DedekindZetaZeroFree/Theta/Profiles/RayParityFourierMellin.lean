module

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.RayParityKernels
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.RayParityTensorTransform
public import DedekindZetaZeroFree.LFunctions.Hecke.ParityReciprocalGammaFactors
public import DedekindZetaZeroFree.Theta.Unfolding.RayParityProductMellin

@[expose] public section

noncomputable section

open Classical NumberField NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity.FourierMellin

variable (K : Type) [Field K] [NumberField K]

theorem fourier (δ : Finset (RayCoset.RealPlaces K)) :
    FourierTransform.fourier (gδ K δ) = fun x ↦ εδ K δ * gδ K δ x := by
  funext x
  exact fourier_gδ K δ x

theorem mellinFactor_mul_reciprocalGamma (δ : Finset (RayCoset.RealPlaces K))
    (s : ℂ) (hs : 1 < s.re) :
    κδ K δ s * hδ K δ s = 1 :=
  κδ_mul_hδ K δ s hs

end DedekindZetaZeroFree.AbelianQuotient.RayParity.FourierMellin

end
