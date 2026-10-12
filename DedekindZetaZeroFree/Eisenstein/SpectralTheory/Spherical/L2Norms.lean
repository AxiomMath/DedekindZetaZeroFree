module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.GradientSquareIntegrability
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.SectionMetricAndEigenfunctions

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualSphericalThreeL2
open KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry KPContActualSectorCutoffGraphLimit
open ResidualSphericalGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

theorem original_l2_norm_finite (Z : smoothSections F ζ hζ U R P H)
    (h2 : MemLp (originalScalar F ζ hζ U R P H Z) 2 R.quotientHaar) :
    normIntegral F ζ hζ U R P H Z.val < ⊤ := by
  have hc : Continuous (scalarRepresentative F ζ hζ U R P H Z.val).val :=
    (continuous_iff F ζ hζ U R P H Z.val).mp (fun i => (Z.property i).continuous)
  apply (finite_integral_iff F ζ hζ U R P H Z.val
    (fun i => (Z.property i).continuous.measurable)).mpr
  apply (memLp_map_measure_iff hc.aestronglyMeasurable
    (KPContSectorQuotientRelationsComparison.piTilde_continuous F ζ hζ U).measurable.aemeasurable).mpr
  exact h2

theorem threeL2_of_native (Z : smoothSections F ζ hζ U R P H) (a : ℂ)
    (h2 : MemLp (originalScalar F ζ hζ U R P H Z) 2 R.quotientHaar)
    (hg : KPContActualCotangentMeasurableFamilies.squareFinite (R := R) (P := P) (gradient Z))
    (heigen : ∀ g, KPMsGreenFlux.casimir F ζ hζ
      (originalScalar F ζ hζ U R P H Z ∘ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) g =
      a * originalScalar F ζ hζ U R P H Z (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) :
    ThreeL2 Z := by
  have h0 := original_l2_norm_finite F ζ hζ U R P H Z h2
  refine ⟨h0, hg, ?_⟩
  rw [ResidualSectionMetric.section_eigen_of_native F ζ hζ U R P H Z a heigen]
  have hs := (BorelL2Sections F ζ hζ U R P H).smul_mem a
    (show Z.val ∈ BorelL2Sections F ζ hζ U R P H from
      ⟨fun i => (Z.property i).continuous.measurable, h0⟩)
  exact hs.2
end DedekindZetaZeroFree.FourierContinuation.ResidualSphericalThreeL2

end
