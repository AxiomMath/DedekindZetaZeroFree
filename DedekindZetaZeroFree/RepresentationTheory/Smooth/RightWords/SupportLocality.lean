module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightInvariantDifferentialWords
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.NativeLieWordReindexing
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open Filter
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingLocality
open KPContActualSphericalRightFieldIdentification
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
local notation "G" => KPSmoothLocalQuotientCharts.ActualCover F ζ hζ

open KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource

private theorem actual_ray_tendsto (b : Fin (groupDimension F)) (g : G) :
    Tendsto (fun t : ℝ => g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single (lieEnumeration F b) 1)))
      (𝓝 0) (𝓝 g) := by
  simp_rw [actual_frame_ray_eq_flow F]
  have hc : Continuous (fun t : ℝ => g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPSmoothActualFlowData.flow F (actualBasisReindex F (lieEnumeration F b)) t)) :=
    continuous_const.mul
      ((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
        (KPSmoothActualFlowData.flow_properties F _).2.2)
  simpa only [ContinuousAt, (KPSmoothActualFlowData.flow_properties F _).1,
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1, mul_one] using
    hc.continuousAt (x := (0 : ℝ))

theorem actualRight_germ_congr (b : Fin (groupDimension F))
    {f h : G → ℂ} {g : G} (he : f =ᶠ[𝓝 g] h) :
    actualRight F ζ hζ b f g = actualRight F ζ hζ b h g := by
  exact (he.comp_tendsto (actual_ray_tendsto b g)).deriv_eq

theorem actualRightWord_germ_congr (w : List (Fin (groupDimension F)))
    {f h : G → ℂ} {g : G} (he : f =ᶠ[𝓝 g] h) :
    actualRightWord F ζ hζ w f =ᶠ[𝓝 g] actualRightWord F ζ hζ w h := by
  induction w with
  | nil => exact he
  | cons b w ih =>
    filter_upwards [ih.eventuallyEq_nhds] with a ha
    exact actualRight_germ_congr b ha

private theorem six_ray_tendsto (b : KPSmoothActualFlowData.B F) (g : G) :
    Tendsto (fun t : ℝ => g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPSmoothActualFlowData.flow F b t)) (𝓝 0) (𝓝 g) := by
  have hc : Continuous (fun t : ℝ => g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPSmoothActualFlowData.flow F b t)) := continuous_const.mul
    ((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
      (KPSmoothActualFlowData.flow_properties F b).2.2)
  simpa only [ContinuousAt, (KPSmoothActualFlowData.flow_properties F b).1,
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1, mul_one] using hc.continuousAt (x := (0 : ℝ))

theorem rightDerivative_germ_congr (b : KPSmoothActualFlowData.B F)
    {f h : G → ℂ} {g : G} (he : f =ᶠ[𝓝 g] h) :
    KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 f g =
      KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 h g :=
  (he.comp_tendsto (six_ray_tendsto b g)).deriv_eq

private theorem rightDerivative_germ (b : KPSmoothActualFlowData.B F)
    {f h : G → ℂ} {g : G} (he : f =ᶠ[𝓝 g] h) :
    KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 f =ᶠ[𝓝 g]
      KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 h := by
  filter_upwards [he.eventuallyEq_nhds] with a ha
  exact rightDerivative_germ_congr b ha

theorem casimir_germ_congr {f h : G → ℂ} {g : G} (he : f =ᶠ[𝓝 g] h) :
    KPMsGreenFlux.casimir F ζ hζ f g = KPMsGreenFlux.casimir F ζ hζ h g := by
  have hd (v : NumberField.InfinitePlace F) (i j : Fin 6) :=
    rightDerivative_germ_congr (v,i) (rightDerivative_germ (v,j) he)
  simp only [KPMsGreenFlux.casimir, hd]

theorem actualRightWord_zero_of_zero_germ (w : List (Fin (groupDimension F)))
    {f : G → ℂ} {g : G} (he : f =ᶠ[𝓝 g] (0 : G → ℂ)) :
    actualRightWord F ζ hζ w f g = 0 := by
  have hz : actualRightWord F ζ hζ w (0 : G → ℂ) = 0 := by
    induction w with
    | nil => rfl
    | cons b w ih =>
      rw [actualRightWord, ih]
      funext a
      change deriv (fun _ : ℝ => (0 : ℂ)) 0 = 0
      exact deriv_const _ _
  simpa only [hz, Pi.zero_apply] using (actualRightWord_germ_congr w he).eq_of_nhds

end DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingLocality

end
