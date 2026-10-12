module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.DifferentialOperators.ScalarLaplacianGraph
public import DedekindZetaZeroFree.Geometry.Hyperbolic.Cotangent.LogarithmicCoframe

@[expose] public section

open scoped BigOperators
noncomputable section
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
  (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

def coframeEvaluation (W : Cotangent F ζ hζ U) (x v : Arch F) : ℂ :=
  ∑ i, ((W (i,0) : ℂ) * (v i).2 + (Real.exp (-(x i).2) : ℂ) *
    ((W (i,1) : ℂ) * (v i).1.re + (W (i,2) : ℂ) * (v i).1.im))

end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

end
