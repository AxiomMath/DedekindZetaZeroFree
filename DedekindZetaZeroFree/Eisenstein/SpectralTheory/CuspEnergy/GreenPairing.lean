module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.RadialTests

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPCompactGreenRadialIntegrability
open KPMeanZeroWeightedEnergy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ} {T : ℝ}

def rawCutoffUpstairs (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (x : HyperbolicChart.Space (KPCuspLogShape.dimension F)) : ℂ :=
  (η (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
    (arch (KPCuspLogShape.dimension F) x)) : ℂ) *
      v.val (arch (KPCuspLogShape.dimension F) x)

def rawCutoffGradientSq (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (p : KPCuspCharts.Coordinates F) : ℝ :=
  let w := HyperbolicChart.differential (KPCuspLogShape.dimension F)
    (rawCutoffUpstairs v η)
    (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))
  ∑ i, ∑ k, ‖w i k‖ ^ 2

def rawWeightedGreenDensity (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (p : KPCuspCharts.Coordinates F) : ℝ :=
  let x := real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p)
  (HyperbolicChart.pairing (KPCuspLogShape.dimension F)
    (HyperbolicChart.differential (KPCuspLogShape.dimension F)
      (rawCutoffUpstairs v (fun t => η t ^ 2)) x)
    (HyperbolicChart.differential (KPCuspLogShape.dimension F)
      (v.val ∘ arch (KPCuspLogShape.dimension F)) x)).re

end DedekindZetaZeroFree.KPCompactGreenRadialIntegrability

end
