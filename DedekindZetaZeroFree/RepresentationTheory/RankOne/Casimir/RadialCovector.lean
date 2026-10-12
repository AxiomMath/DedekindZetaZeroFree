module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
namespace DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

def normalRadial (c g : Cover F ζ hζ) : ℝ :=
  Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) *
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (fun i => KPArch.action
        (KPSmoothLocalQuotientCharts.archProjection F ζ hζ (c⁻¹ * g)
          (KPCusp.complexPlace F i)).out (0,0)))

def normalRadialJet (c : Cover F ζ hζ) (w : NumberField.InfinitePlace F)
    (l : Fin 6) (g : Cover F ζ hζ) : ℝ :=
  deriv (fun t : ℝ => normalRadial c
    (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPSmoothActualFlowData.flow F (w,l) t))) 0

end DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient

end
