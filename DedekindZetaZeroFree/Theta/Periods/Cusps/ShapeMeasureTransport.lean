module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Angular.ShellProbabilityMeasures

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.CurrentBoundaryShapeTransport
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable (M : NativeMeasuredSource F ζ hζ R P) (V : Level F ζ hζ)

private theorem full_shape_measurable :
    Measurable (M.shape V ∘ fullToLevel F ζ hζ (nativeDatum F ζ hζ)
      (cofinalLevel F ζ hζ V)) :=
  (M.shape_measurable V).comp (KPMsActualAngularShellSource.fullToLevel_measurable _ _)

private theorem full_shape_map :
    Measure.map (M.shape V ∘ fullToLevel F ζ hζ (nativeDatum F ζ hζ)
      (cofinalLevel F ζ hζ V)) (fullNu M) = normalizedShapeBeta M V := by
  rw [← Measure.map_map (M.shape_measurable V)
    (KPMsActualAngularShellSource.fullToLevel_measurable _ _),
    nu_from_full, shape_measure]

theorem averaged_shape_integral
    (dk : Measure (KPMsGreenFlux.K F)) [SFinite dk]
    (Ψ : KPMsFixedHaarDisintegration.Omega
      (nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V) ×
        KPMsGreenFlux.K F → ℂ)
    (hΨ : Integrable Ψ ((normalizedShapeBeta M V).prod dk)) :
    (∫ ω, ∫ k, Ψ (M.shape V
      (fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) ω), k)
        ∂dk ∂fullNu M) =
      ∫ η, ∫ k, Ψ (η,k) ∂dk ∂normalizedShapeBeta M V := by
  have hm := full_shape_map M V
  have ha := hΨ.integral_prod_left.aestronglyMeasurable
  rw [← hm] at ha ⊢
  exact (integral_map (full_shape_measurable M V).aemeasurable ha).symm

theorem ae_fullNu_of_shells
    (Y : ℝ) (hY : OffsetAdmissible F ζ hζ R P (nativeRecipe F ζ hζ R P) V Y)
    (q : FullOmega F ζ hζ (nativeDatum F ζ hζ) → Prop)
    (hq : MeasurableSet {ω | q ω})
    (hshell : ∀ j : NativeCusp F ζ hζ R P (nativeRecipe F ζ hζ R P) V,
      ∀ᵐ x ∂ R.quotientHaar.restrict
        (cuspShell F ζ hζ R P (nativeRecipe F ζ hζ R P) V j Y),
          q (fullCoordinate F ζ hζ R P (nativeRecipe F ζ hζ R P) V j Y x)) :
    ∀ᵐ ω ∂fullNu M, q ω := by
  change ∀ᵐ ω ∂(fullMass M)⁻¹ • M.full, q ω
  apply Measure.ae_smul_measure
  rw [full_from_source M V Y hY]
  apply ae_finsetSum_measure_iff.mpr
  intro j hj
  apply Measure.ae_smul_measure
  exact (ae_map_iff (fullCoordinate_aemeasurable F ζ hζ R P
    (nativeRecipe F ζ hζ R P) V j Y hY) hq).mpr (hshell j)

end DedekindZetaZeroFree.CurrentBoundaryShapeTransport

end
