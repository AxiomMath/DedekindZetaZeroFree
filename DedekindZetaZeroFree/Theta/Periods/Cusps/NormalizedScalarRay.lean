module

public import DedekindZetaZeroFree.Theta.Periods.Cusps.ScalarRadialNormalization

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped Classical NumberField NNReal ENNReal Topology BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.CurrentBoundaryFrame
open KPMsGreenFlux KPContFlatArchDiagonalMultiplier KPMsActualAngularSource
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable (φ : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
variable (ha : ∀ (u : NumberField.InfinitePlace F → ℝ) g,
  φ ((aInfinity F ζ hζ u).val * g) =
    Complex.exp ((2:ℂ) * ((∑v, u v : ℝ):ℂ)) * φ g)
variable (hn : ∀ n g, φ (KPGlobalTorusFunctionData.N F ζ hζ n * g) = φ g)
include ha hn in
theorem scalar_normalized_actual_ray
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (j : Cusps A) (p : KPCuspCharts.Cross F) (k : K F)
    (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup) (r : ℝ) (hr : 0<r) :
    φ (framedNormalization F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ) B
      (cuspRepresentative A j) (KPBoundedCuspFrames.actualCuspLift A j p k r *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val.val)) =
      ((cuspOffset A j ε u).val:ℂ)⁻¹ *
        φ (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (fun i => (k i).val) *
          (KPBoundedCuspFrames.actualFiniteRepresentative A j).val *
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val.val) := by
  have hray : (framedRadius F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ)
      (cuspRepresentative A j) (KPBoundedCuspFrames.actualCuspLift A j p k r *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val.val)).val =
      (cuspOffset A j ε u).val * r := by
    simpa only [framedRadius,actualPoint,mul_assoc] using actual_ray_norm A j p k ε u r hr
  rw [scalar_normalization φ ha,hray]
  rw [show (cuspRepresentative A j)⁻¹ *
      (KPBoundedCuspFrames.actualCuspLift A j p k r *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val.val) =
      (cuspRepresentative A j)⁻¹ * KPBoundedCuspFrames.actualCuspLift A j p k r *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val.val by group]
  rw [scalar_corrected_ray φ ha hn A j p k ε u r hr]
  push_cast
  have hc : ((cuspOffset A j ε u).val:ℂ) ≠ 0 := by exact_mod_cast (cuspOffset A j ε u).property.ne'
  have hr' : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
end DedekindZetaZeroFree.CurrentBoundaryFrame

end
