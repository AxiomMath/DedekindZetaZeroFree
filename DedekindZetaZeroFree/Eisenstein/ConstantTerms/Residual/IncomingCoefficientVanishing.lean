module

public import DedekindZetaZeroFree.Eisenstein.Residues.Pairings.KernelMean
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residual.RadialHaarAndCutoffIntegrals

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPContFlatCuspIncomingEvaluation
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (j : Cusps F ζ hζ C R P H U)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
theorem incoming_zero_scalar (v : S) (t : ℝ) (shape : KPCuspCharts.Shape F) :
    (W F ζ hζ C R P H U j ι 0 v t shape).val 0 =
      KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) 0 t *
      (zeroProjection F ζ hζ C R P H U j
        (sheetEvaluation F ζ hζ C R P H U j ι 0 v)).val 0 := by
  rw [incoming_formula F ζ hζ C R P H U j ι 0 (by
    norm_num [KPContinuation.spectralDomain]
    skip) v t shape, b_formula]
  rfl

end DedekindZetaZeroFree.KPContFlatCuspIncomingEvaluation

end
