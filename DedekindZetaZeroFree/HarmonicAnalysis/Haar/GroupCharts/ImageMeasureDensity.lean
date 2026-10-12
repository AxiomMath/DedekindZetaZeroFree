module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LieGroups.SmoothChartDensity
public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.RightInvariantFieldCoordinates

@[expose] public section

noncomputable section
open MeasureTheory Topology
open scoped Classical NumberField Manifold ContDiff ENNReal
namespace DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2
open KPContActualSphericalRightFieldIdentification
open LocalQuotientCharts.ExponentialHaarFrame

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem original_chart_raw_haar_density (D : GroupChart F ζ hζ U R P H)
    (μ : Measure (KPSmoothLocalQuotientCharts.ArchGroup F)) (hμ : μ.IsHaarMeasure) :
    ∃ ρ : KPSmoothLocalQuotientCharts.Coordinates F → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) ρ D.exponential.chart.source ∧
      (∀ x ∈ D.exponential.chart.source, 0 < ρ x) ∧
      Measure.map D.exponential.chart.symm (μ.restrict D.exponential.chart.target) =
        (volume.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict
          D.exponential.chart.source := by
  letI := actualLieChartedSpace F
  letI := actualLieGroup F
  obtain ⟨E, he, hi⟩ := D.inverse_smooth
  have hE : ContMDiffOn (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
      (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞) E E.source := by
    apply ((contMDiff_const (c := D.groupCenter)).mul
      (actualLieData F).exponential_smooth).contMDiffOn.congr
    intro a ha
    have hh := D.exponential.exponential_formula a (he ▸ ha)
    rw [← he] at hh
    exact hh.trans (congrArg (D.groupCenter * ·)
      (congrFun (actualLieData_exponential F) a)).symm
  have hC : ∀ g, chartAt (KPSmoothLocalQuotientCharts.Coordinates F) g =
      (rawAffineChart F g).symm :=
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (raw_lie_exponential_data F)))).2.2
  obtain ⟨ρ, hρ, hp, hm⟩ := @raw_smooth_chart_haar_density F _ _
    (actualLieChartedSpace F) (actualLieGroup F) hC μ hμ E hE hi
  exact ⟨ρ, he ▸ hρ, he ▸ hp, he ▸ hm⟩

theorem group_coordinates_volume_preserving (F : Type) [Field F] [NumberField F] :
    MeasurePreserving (groupCoordinates F) volume volume := by
  have hp := measurePreserving_piCongrLeft
    (fun _ : LieIndex F => (volume : Measure ℝ))
    (lieEnumeration F)
  have he : MeasurePreserving (EuclideanSpace.equiv
      (Fin (groupDimension F)) ℝ) volume volume := PiLp.volume_preserving_ofLp _
  have hp' : MeasurePreserving
      (ContinuousLinearEquiv.piCongrLeft ℝ
        (fun _ : LieIndex F => ℝ)
        (lieEnumeration F)) volume volume := by
    exact hp
  exact hp'.comp he

theorem original_chart_image_measure_density (D : GroupChart F ζ hζ U R P H)
    (μ : Measure (KPSmoothLocalQuotientCharts.ArchGroup F)) (hμ : μ.IsHaarMeasure) :
    ∃ ρ : KPContLocalNorm.Space (groupDimension F) → ℝ,
      ContinuousOn ρ D.T.carrier ∧ (∀ x ∈ D.T.carrier, 0 < ρ x) ∧
      ∀ S : Set (KPContLocalNorm.Space (groupDimension F)), MeasurableSet S →
        S ⊆ D.T.carrier →
        μ ((fun x => D.exponential.chart (groupCoordinates F x)) '' S) =
          ∫⁻ x in S, ENNReal.ofReal (ρ x) := by
  obtain ⟨r, hr, hp, hm⟩ := original_chart_raw_haar_density D μ hμ
  let L := groupCoordinates F
  let e := D.exponential.chart
  have hLT : Set.MapsTo L D.T.carrier e.source := by
    intro x hx
    exact D.closure_source ⟨x, subset_closure hx, rfl⟩
  refine ⟨r ∘ L, hr.continuousOn.comp L.continuous.continuousOn hLT,
    fun x hx => hp (L x) (hLT hx), ?_⟩
  intro S hS hST
  have hLS : L '' S ⊆ e.source := Set.image_subset_iff.mpr (hLT.mono_left hST)
  have hLSm : MeasurableSet (L '' S) := L.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hS
  have hpre : e.symm ⁻¹' (L '' S) ∩ e.target = e '' (L '' S) := by
    ext y
    constructor
    · rintro ⟨hy, hyt⟩
      exact ⟨e.symm y, hy, e.right_inv hyt⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, e.map_source (hLS hx)⟩
      change e.symm (e x) ∈ L '' S
      rwa [e.left_inv (hLS hx)]
  have het : IsOpen e.target := by
    letI := actualLieChartedSpace F
    obtain ⟨E, he, _⟩ := D.inverse_smooth
    change IsOpen D.exponential.chart.target
    rw [← he]
    exact E.open_target
  have hraw : μ (e '' (L '' S)) = ∫⁻ x in L '' S, ENNReal.ofReal (r x) := by
    have hh := congrArg (fun m : Measure (KPSmoothLocalQuotientCharts.Coordinates F) => m (L '' S)) hm
    change (Measure.map e.symm (μ.restrict e.target)) (L '' S) =
      ((volume.withDensity (fun x => ENNReal.ofReal (r x))).restrict e.source) (L '' S) at hh
    have hme : AEMeasurable e.symm (μ.restrict e.target) :=
      e.continuousOn_invFun.aemeasurable het.measurableSet
    rw [Measure.map_apply_of_aemeasurable hme hLSm,
      Measure.restrict_apply' het.measurableSet, hpre,
      Measure.restrict_apply hLSm, Set.inter_eq_left.mpr hLS,
      withDensity_apply _ hLSm] at hh
    exact hh
  change μ ((e ∘ L) '' S) = _
  rw [Set.image_comp]
  rw [hraw]
  exact ((group_coordinates_volume_preserving F).setLIntegral_comp_emb
    L.toHomeomorph.measurableEmbedding (fun x => ENNReal.ofReal (r x)) S).symm

end DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2

end
