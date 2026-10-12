module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspDivergence.CutoffScalarFlux

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical Topology

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice
open KPMeanZeroWeightedEnergy HyperbolicChart

def radialCoefficient (F : Type) [Field F] [NumberField F]
    (W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F))
    (c : KPCuspCharts.Cross F) (t : ℝ) : ℝ :=
  (∑ i : Fin (KPCuspLogShape.dimension F),
    (W (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, t))) i 0).re) /
      (KPCuspLogShape.dimension F : ℝ)

def tangentialDivergence (F : Type) [Field F] [NumberField F]
    (W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F))
    (c : KPCuspCharts.Cross F) (t : ℝ) : ℝ :=
  let d := KPCuspLogShape.dimension F
  let x := real d (KPCuspCharts.toArch F (c, t))
  ∑ i : Fin d,
    ((coordinateDerivative d i 2 (fun q => W q i 0) x).re -
      (∑ j : Fin d, (coordinateDerivative d j 2 (fun q => W q i 0) x).re) / (d : ℝ) +
      ((Real.exp (x (i, 2)) : ℂ) *
        coordinateDerivative d i 0 (fun q => W q i 1) x).re +
      ((Real.exp (x (i, 2)) : ℂ) *
        coordinateDerivative d i 1 (fun q => W q i 2) x).re)

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice

end
