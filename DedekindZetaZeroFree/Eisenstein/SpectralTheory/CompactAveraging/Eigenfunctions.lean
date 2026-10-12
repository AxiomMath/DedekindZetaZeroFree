module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactAveraging.Casimir
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightTranslation.CasimirCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualAverageEigen
open KPLiteralRaw
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩
theorem average_native_eigen
    (K : Subgroup (G F ζ hζ)) (hK : IsCompact (K : Set (G F ζ hζ)))
    (μ : Measure K) [IsFiniteMeasure μ] (f : G F ζ hζ → ℂ)
    (hf : Smooth F ζ hζ f) (a : ℂ)
    (he : ∀g, KPMsGreenFlux.casimir F ζ hζ f g = a*f g) (g : G F ζ hζ) :
    KPMsGreenFlux.casimir F ζ hζ (ResidualRawAverage.average F ζ hζ K μ f) g =
      a * ResidualRawAverage.average F ζ hζ K μ f g := by
  rw [ResidualAverageCasimir.casimir_average F ζ hζ K hK μ f hf g]
  simp_rw [ResidualFullGroupTranslation.casimir_right_translate f hf.2.1,he]
  exact integral_const_mul _ _

end DedekindZetaZeroFree.FourierContinuation.ResidualAverageEigen

end
