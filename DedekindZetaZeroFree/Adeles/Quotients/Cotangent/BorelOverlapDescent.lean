module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.OverlapNullEquivalence
public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.IntegralDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentBorelOverlapDescent

open KPContActualCotangentCountableShrinking
open KPContCotangentOverlapRationalBranches KPContCotangentOverlapNullEquivalence

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

structure NonsingularEnumeration (a b : ShrunkChart F ζ hζ U R P H)
    extends Enumeration a b where
  nonsingular : ∀ k, NullEquivalence (branch k) (properties k)

end DedekindZetaZeroFree.KPContActualCotangentBorelOverlapDescent

namespace DedekindZetaZeroFree

open KPContActualCotangentCountableShrinking
open KPContActualCotangentBorelOverlapDescent
open KPContCotangentFiniteQuotientBorel KPContCotangentChartDescentIntegrals

section LevelRealizationHelper

open KPContSectorCoveredQuotientVocabulary KPContSectorQuotientRelationsComparison
open KPContSectorFixedPushforwardSupport KPContSectorScalarLineAlgebra
open KPContSectorSmoothFramesSupport KPMsFixedHaarDisintegration

private theorem levelRealization_of_recipe
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :
    KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H := by
  have hpos : R.quotientHaar.IsOpenPosMeasure :=
    (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1
  refine
    { actual_projection := rfl
      quotient_projection := (piTilde_isOpenMap F ζ hζ U).isQuotientMap
        (piTilde_continuous F ζ hζ U) (piTilde_surjective F ζ hζ U)
      covered_pushforward := rfl
      support := levelSupport F ζ hζ R P hpos U
      local_finiteness :=
        KPContSectorFixedMeasureLocalFiniteness.levelLocalFiniteness F ζ hζ R P H U
      central_measure_preserving := fun ε =>
        KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε
      sector_closed := KPContSectorClosedLpSubspace.H_isClosed F ζ hζ R U
      sector_complete := inferInstance
      sector_membership := KPContSectorClosedLpSubspace.mem_H_iff F ζ hζ R U
      line_l2 := kp_cont_sector_line_l2_isometry F ζ hζ U R P H
      sector_line_norm := by
        intro u
        obtain ⟨g, hg, hgLp, hgu, f, hf, hfLp, hfavg, hfLp_toLp, heq, hzero⟩ :=
          KPContSectorExactBorelRepresentatives.exists_exact_borel_representative
            F ζ hζ R U u
        let f' : GenuineCoveredScalars F ζ hζ U := ⟨f, heq⟩
        let Fb : KPContSectorLineL2Isometry.BorelL2Scalars F ζ hζ U R :=
          ⟨f', ⟨hf, by simpa [f'] using hfLp⟩⟩
        have hFb : Fb.property.2.toLp Fb.val.val =
            (u : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) := by
          simpa [Fb, f'] using hfLp_toLp
        refine ⟨KPContSectorLineL2Isometry.borelS F ζ hζ U R P H Fb, ?_, ?_⟩
        · exact KPContSectorLineL2Isometry.sectorLineIsometry_representative
            F ζ hζ U R P H u Fb hFb
        · rw [show ‖u‖ =
              ‖KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ U R P H u‖ from
              (LinearIsometryEquiv.norm_map _ u).symm,
            KPContSectorLineL2Isometry.sectorLineIsometry_representative
              F ζ hζ U R P H u Fb hFb]
          exact (kp_cont_sector_line_l2_isometry F ζ hζ U R P H).norm_formula
            (KPContSectorLineL2Isometry.borelS F ζ hζ U R P H Fb)
      norm_integrals := fun f hf =>
        kp_cont_sector_fixed_line_norm_integrals F ζ hζ U R P H f hf
      orbit_stabilizer := fun v =>
        KPContSectorFiniteOrbitIntegral.orbit_card_mul_stabilizer_card F ζ hζ U v
      fiber_repetitions := fun v w h =>
        KPContSectorFiniteOrbitIntegral.fiber_point_repetitions F ζ hζ U v w h
      finite_fiber_average := fun ψ v =>
        KPContSectorFiniteOrbitIntegral.centralAverage_eq_distinctOrbitAverage F ζ hζ U ψ v
      scalar_descent := fun f x c => J_apply F ζ hζ U f x c
      group_lift := fun f a c => group_lift_formula F ζ hζ U f a c
      smooth_realization := fun f => smoothS_apply F ζ hζ U R P H f
      smooth_iff := fun f => smooth_iff F ζ hζ U R P H f
      smooth_actual_charts :=
        (kp_cont_sector_smooth_frames_support F ζ hζ U R P H).2.1
      phase_formula := (kp_cont_sector_smooth_frames_support F ζ hζ U R P H).2.2.1
      chart_exists := fun i x =>
        KPContSectorPhaseComponentCharts.orbifoldChart_exists F ζ hζ U R P H i x
      chart_isotropy_finite := fun i x O =>
        KPContSectorPhaseComponentCharts.chart_stabilizer_finite F ζ hζ U R P H i x O
      frame_unitary := fun x v => liftFrame_unitary F ζ hζ U x v
      frame_equivariant := fun i γ x v => liftFrame_equivariant F ζ hζ U R P H i γ x v
      chart_restriction := fun f i x O m y =>
        orbifold_restriction_commutes F ζ hζ U R P H f i x O m y
      cusp_restriction := fun f i j p t =>
        cusp_restriction_commutes F ζ hζ U R P H f i j p t
      cusp_transition := fun s i j g p t =>
        cuspCoefficient_transition F ζ hζ U R P H s i j g p t
      cusp_atlas_overlap := fun s i j => actual_cusp_atlas_overlap F ζ hζ U R P H s i j
      support_image := fun f => tsupport_sectionNorm F ζ hζ U R P H f
      compact_support := fun f => hasCompactSupport_iff F ζ hζ U R P H f }

theorem actual_levelRealization_of_recipe
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :
    KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H :=
  levelRealization_of_recipe F ζ hζ U R P H

end LevelRealizationHelper

theorem kp_cont_actual_cotangent_borel_overlap_descent
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (cover : CountableCover F ζ hζ U R P H)
    (S : Type*) [MeasurableSpace S] :
    ∀ a : ShrunkChart F ζ hζ U R P H,
      (∀ n : ℕ, Nonempty (KPContCotangentCorrectedNullEquivalence.NonsingularEnumeration2
        a (cover.chart n))) ∧
      (∀ f : a.domain → S, Measurable f →
        (∀ σ y, f (a.action σ y) = f y) → BorelDescends a.quotientMap f) ∧
      ChartDescentIntegrals a := by
  have realization :
      KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H :=
    levelRealization_of_recipe F ζ hζ U R P H
  intro a
  have ha : a.Properties := every_shrunkChart_properties F ζ hζ U R P H a
  refine ⟨?_, ?_, ?_⟩
  · intro n
    obtain ⟨e⟩ :=
      kp_cont_cotangent_overlap_rational_branches F ζ hζ μG hμG U R hR P H
        realization cover a ha n
    exact ⟨KPContCotangentCorrectedNullEquivalence.withNonsingularity2 e⟩
  · intro f hf hinv
    exact (kp_cont_cotangent_finite_quotient_borel F ζ hζ U R P H S).2 a f hf hinv
  · exact kp_cont_cotangent_chart_descent_integrals F ζ hζ U R P H a

end DedekindZetaZeroFree

end
