module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residual.IncomingProjection
public import DedekindZetaZeroFree.Eisenstein.Residues.Spherical.HilbertBoundaryCenters

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualSphericalBoundaryBeta
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option quotPrecheck false
open KPContFlatCuspIncomingEvaluation
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "V" => atlasLevel F ζ hζ C R P H U
local notation "A" => H.atlas V
local notation "β" => (H.disintegration V).beta
local notation "Ω" => KPMsFixedHaarDisintegration.Omega A

theorem mass_probability (f : Ω → ℂ) :
    ((β Set.univ).toReal : ℂ) *
      (∫ω, f ω ∂KPMsFixedHaarDisintegration.probability A β) = ∫ω,f ω ∂β := by
  let := (H.disintegration V).finite_beta
  have hm : (β Set.univ).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr
    ⟨(H.disintegration V).positive_beta,measure_ne_top β Set.univ⟩
  rw [KPMsFixedHaarDisintegration.probability,integral_smul_measure,ENNReal.toReal_inv]
  change ((β Set.univ).toReal : ℂ) * (((β Set.univ).toReal)⁻¹ : ℝ) • (∫ω,f ω ∂β) = _
  simp only [Complex.real_smul,Complex.ofReal_inv]
  rw [← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hm),one_mul]

theorem projected_boundary_eq_beta
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (b : Cusps F ζ hζ C R P H U → ℂ) :
    ((β Set.univ).toReal : ℂ) *
      (∫ω : Ω,
        (zeroProjection F ζ hζ C R P H U ω.1
          (sheetEvaluation F ζ hζ C R P H U ω.1
            (LinearMap.toSpanSingleton ℂ _ v) 0 (1:ℂ))).val 0 * star (b ω.1)
        ∂KPMsFixedHaarDisintegration.probability A β) =
      ∫ω : Ω, (KPContFlatSourceRecipe.flatR F ζ hζ 0 v.val).val
        (finiteRepresentative F ζ hζ C R P H U ω.1 1).val * star (b ω.1) ∂β := by
  rw [mass_probability]
  apply integral_congr_ae
  filter_upwards with ω
  rw [ResidualIncomingProjection.projected_sheet_evaluation F ζ hζ C R P H U ω.1
    (LinearMap.toSpanSingleton ℂ _ v) 0 (by norm_num [KPContinuation.spectralDomain]) (1:ℂ)]
  congr 1
  change KPContFlatCommonLevelKernel.L F ζ hζ U (LinearMap.toSpanSingleton ℂ _ v) 0 1 _ = _
  simp [KPContFlatCommonLevelKernel.L_formula,KPContFlatSourceRecipe.flatR_formula]
end DedekindZetaZeroFree.FourierContinuation.ResidualSphericalBoundaryBeta

end
