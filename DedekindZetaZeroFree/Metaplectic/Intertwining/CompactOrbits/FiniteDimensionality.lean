module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.HarishChandraHeckeCore.FiniteDimensionalCompactOrbits

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical NumberField ENNReal NNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ScatteringResidue
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {T : KPMsRationalCompactCrossPairing.ModelData F ζ hζ}
variable {D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ T D R P H)

variable {S : Submodule ℂ (KPMsFixedHaarDisintegration.X F ζ hζ → ℂ)}

theorem source_raw_compact_orbit_finiteDimensional_public
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ D) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      (fun k : D.K => fun g => f.val.val (g * k.val)))) :=
  SourceCoreCompactOrbit.source_finiteDimensional f

end DedekindZetaZeroFree.KPGlobalResidualKernel.ScatteringResidue

end
