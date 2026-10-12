module

public import DedekindZetaZeroFree.Theta.Periods.Cusps.ShapeMeasureTransport
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.BoundaryFrameAveraging

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualFiniteAnchor
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable (V : Level F ζ hζ)

def anchorAverage (dk : Measure (KPMsGreenFlux.K F)) (φ : G F ζ hζ → ℂ)
    (ω : KPMsFixedHaarDisintegration.Omega
      (nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V)) : ℂ :=
  ∫k, φ (KPMsGreenFlux.compactInsertion F ζ hζ k *
    (KPBoundedCuspFrames.actualFiniteRepresentative
      (nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V) ω.1).val) ∂dk

end DedekindZetaZeroFree.FourierContinuation.ResidualFiniteAnchor

end
