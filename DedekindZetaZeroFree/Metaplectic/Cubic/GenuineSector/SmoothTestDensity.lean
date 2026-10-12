module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.SectionSpaces.CompactTailTruncation
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.SectionSpaces.FiniteChartApproximation

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree

open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings

theorem kp_cont_actual_sector_test_density
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    (∀ (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) (ε : ℝ), 0 < ε →
      ∃ φ : S_U F ζ hζ U R P H, ‖u - iota φ‖ < ε) ∧
    (∀ (v : KPContActualSectorCotangentL2.V F ζ hζ U R P H) (ε : ℝ), 0 < ε →
      ∃ W : T_U F ζ hζ U R P H, ‖v - j W‖ < ε) ∧
    DenseRange (iota (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)) ∧
    DenseRange (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)) := by
  have approximate :
      ∀ (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
        (v : KPContActualSectorCotangentL2.V F ζ hζ U R P H) (ε : ℝ), 0 < ε →
        ∃ (φ : S_U F ζ hζ U R P H) (W : T_U F ζ hζ U R P H),
          ‖u - iota φ‖ < ε ∧ ‖v - j W‖ < ε := by
    intro u v ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    obtain ⟨K, hK, hKm, s, r, hs, hr, hu, hv⟩ :=
      RepresentationTheory.ActualSectorTestDensity.compact_tail F ζ hζ μG hμG U R hR P H
        realization u v (ε / 2) hhalf
    obtain ⟨n, C, _, _, ⟨partition⟩⟩ :=
      kp_cont_actual_sector_finite_support_partition F ζ hζ U R P H K Set.univ
        hK isOpen_univ (Set.subset_univ K)
    obtain ⟨f, w, hf, hw⟩ :=
      RepresentationTheory.ActualSectorTestDensity.finite_chart_approximation F ζ hζ μG hμG U R hR P H
        realization K Set.univ hK hKm isOpen_univ n C partition s r hs hr (ε / 2) hhalf
    refine ⟨∑ i, scalarZeroExtension (C i) (f i),
      ∑ i, cotangentZeroExtension (C i) (w i), ?_, ?_⟩
    · calc
        ‖u - iota (∑ i, scalarZeroExtension (C i) (f i))‖ ≤
            ‖u - KPContSectorLineL2Isometry.toSector F ζ hζ U R P H s‖ +
            ‖KPContSectorLineL2Isometry.toSector F ζ hζ U R P H s -
              iota (∑ i, scalarZeroExtension (C i) (f i))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add hu hf
        _ = ε := add_halves ε
    · calc
        ‖v - j (∑ i, cotangentZeroExtension (C i) (w i))‖ ≤
            ‖v - KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r‖ +
            ‖KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r -
              j (∑ i, cotangentZeroExtension (C i) (w i))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add hv hw
        _ = ε := add_halves ε
  have scalarApprox :
      ∀ (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) (ε : ℝ), 0 < ε →
        ∃ φ : S_U F ζ hζ U R P H, ‖u - iota φ‖ < ε := by
    intro u ε hε
    obtain ⟨φ, _, hφ, _⟩ := approximate u 0 ε hε
    exact ⟨φ, hφ⟩
  have cotangentApprox :
      ∀ (v : KPContActualSectorCotangentL2.V F ζ hζ U R P H) (ε : ℝ), 0 < ε →
        ∃ W : T_U F ζ hζ U R P H, ‖v - j W‖ < ε := by
    intro v ε hε
    obtain ⟨_, W, _, hW⟩ := approximate 0 v ε hε
    exact ⟨W, hW⟩
  refine ⟨scalarApprox, cotangentApprox, ?_, ?_⟩
  · exact Metric.denseRange_iff.mpr (by simpa only [dist_eq_norm] using scalarApprox)
  · exact Metric.denseRange_iff.mpr (by simpa only [dist_eq_norm] using cotangentApprox)

end DedekindZetaZeroFree

end
