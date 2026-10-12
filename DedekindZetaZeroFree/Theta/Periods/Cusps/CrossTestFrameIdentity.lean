module

public import DedekindZetaZeroFree.Theta.Periods.Cusps.CrossTestIntegralTransport

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.CurrentBoundaryShapeTransport
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}

theorem frame_eq_crossTest
    (M : NativeMeasuredSource F ζ hζ R P) (V : Level F ζ hζ)
    (φ : G F ζ hζ → ℂ)
    (haφ : ∀ (u : NumberField.InfinitePlace F → ℝ) g,
      φ ((KPContFlatArchDiagonalMultiplier.aInfinity F ζ hζ u).val * g) =
        Complex.exp ((2:ℂ) * ((∑v,u v:ℝ):ℂ)) * φ g)
    (hnφ : ∀ n g, φ (KPGlobalTorusFunctionData.N F ζ hζ n * g) = φ g)
    (hcφ : ∀ ε g, φ (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g) = φ g)
    (huφ : ∀ (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ V) g, φ (g*u.val) = φ g)
    (dk : Measure (KPMsGreenFlux.K F)) [dk.IsHaarMeasure]
    (j : NativeCusp F ζ hζ R P (nativeRecipe F ζ hζ R P) V) (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P (nativeRecipe F ζ hζ R P) V Y)
    (x : KPSmoothLocalQuotientCharts.X F ζ hζ)
    (hx : x ∈ cuspShell F ζ hζ R P (nativeRecipe F ζ hζ R P) V j Y) :
    (∫ k, φ (framedNormalization F ζ hζ (nativeDatum F ζ hζ)
      (nativeDisintegration F ζ hζ R P (nativeRecipe F ζ hζ R P) V).radial
      (KPMsActualCuspSource.rationalLift F ζ hζ
        (((nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V).cuspAtlas j.1).representative j.2))
      (actualFrame F ζ hζ R P (nativeRecipe F ζ hζ R P) V j Y x *
        KPMsGreenFlux.compactInsertion F ζ hζ k)) ∂dk) =
    ∫ k, crossTest (R:=R) (P:=P) V φ
      (M.shape V (fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V)
        (fullCoordinate F ζ hζ R P (nativeRecipe F ζ hζ R P) V j Y x)),k) ∂dk := by
  rw [CurrentNativeBoundaryFrame.native_frame_average R P (nativeRecipe F ζ hζ R P) V
    φ haφ hnφ hcφ huφ dk j Y x hx]
  simp only [crossTest,cross_shape_cusp M V Y hY j x hx,integral_const_mul]
end DedekindZetaZeroFree.CurrentBoundaryShapeTransport

end
