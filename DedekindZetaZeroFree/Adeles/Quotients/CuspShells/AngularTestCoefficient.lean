module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.CuspTestCoarea

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal ENNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsNativeOffsetMass
open KPMsActualAngularSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (S : NativeRecipe F ζ hζ R P)

namespace CoefficientAssembly
open KPMsActualCuspSource KPMsActualAngularDescentSource
open KPCompactStabilizerHaarSources KPActualComponentHaarSources
attribute [local instance] KPCompactStabilizerHaarSources.groupMeasurableSpace
  KPCompactStabilizerHaarSources.groupBorelSpace
variable {F ζ hζ R P}
local instance : MulAction (KPCuspArithmetic.PGL2 F) (KPArch.Space (KPCuspLogShape.dimension F)) :=
  KPCuspSiegel.instMulActionPGL2SpaceDimension F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
local instance : BorelSpace (FullOmega F ζ hζ (nativeDatum F ζ hζ)) := ⟨rfl⟩

end CoefficientAssembly

theorem fullShell_test_coefficient
    (V : Level F ζ hζ)
    (φ : FullOmega F ζ hζ (nativeDatum F ζ hζ) → ℝ≥0∞) (hφ : Measurable φ) :
    ∃ a : ℝ≥0∞, ∀ (Y : ℝ), OffsetAdmissible F ζ hζ R P S V Y →
      (∫⁻ ω, φ ω ∂fullShell F ζ hζ R P S V Y) = a := by
  classical
  have hcoeff := fun j => ShellTestCoarea.cusp_test_coefficient S V j φ hφ
  choose a ha using hcoeff
  refine ⟨∑ j, a j, ?_⟩
  intro Y hY
  rw [fullShell, lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro j _
  rw [lintegral_smul_measure, lintegral_map' hφ.aemeasurable
    (fullCoordinate_aemeasurable F ζ hζ R P S V j Y hY)]
  exact ha j Y hY

end DedekindZetaZeroFree.KPMsNativeOffsetMass

end
