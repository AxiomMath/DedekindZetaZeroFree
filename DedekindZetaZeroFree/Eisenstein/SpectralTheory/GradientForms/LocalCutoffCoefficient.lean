module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Friedrichs.HaarCoreLocalizers

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPContActualFormLocalRestrictionCompact
attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU
open KPContActualFixedHaarCoreLocalizers KPContSectorLineL2Isometry
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
variable (K : Set (X_U F ζ hζ U)) (hK : IsCompact K)

def actualLocalCoefficient (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count)
    (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H) :
    KPCoreChartLocalizers.E (A.chart i).n → ℂ := fun x =>
  (A.cutoff i x : ℂ) * (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val
    ((A.chart i).coordinates x)

include μG hμG hR realization in
theorem actualLocalCoefficient_smooth (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count)
    (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H) :
    ContDiff ℝ (⊤ : ℕ∞) (actualLocalCoefficient F ζ hζ U R P H K hK A i f) := by
  have hs := (kp_cont_actual_sector_smooth_test_modules F ζ hζ μG hμG U R hR P H realization).scalar_smooth f
  let g := actualLocalCoefficient F ζ hζ U R P H K hK A i f
  have hcut : ContDiff ℝ (⊤ : ℕ∞) (fun x => (A.cutoff i x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (A.smooth_cutoff i)
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (A.cutoff i)
  · have hxe : x ∈ (A.chart i).extendedDomain := (A.chart i).closed_ball_in_extension
      (subset_closure (A.support_cutoff i hx))
    exact hcut.contDiffAt.mul ((hs (A.chart i).component).contDiffAt.comp x
      ((A.chart i).smooth_coordinates.contDiffAt ((A.chart i).open_extendedDomain.mem_nhds hxe)))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [actualLocalCoefficient, hy]

end DedekindZetaZeroFree.KPContActualFormLocalRestrictionCompact

end
