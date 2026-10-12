module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Quotients.CentralOrbitHomeomorphism

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPContSectorFixedPushforwardSupport

open KPContSectorCoveredQuotientVocabulary
open KPContSectorQuotientRelationsComparison

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

instance instMeasurableSpaceCentralOrbitQuotient
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    MeasurableSpace (CentralOrbitQuotient F ζ hζ U) := borel _

instance instBorelSpaceCentralOrbitQuotient
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    BorelSpace (CentralOrbitQuotient F ζ hζ U) := ⟨rfl⟩

def coveredMeasure (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    Measure (CoveredSpherical F ζ hζ U) :=
  Measure.map (piTilde F ζ hζ U) R.quotientHaar

def orbitProjection (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    CoveredSpherical F ζ hζ U → CentralOrbitQuotient F ζ hζ U :=
  Quotient.mk (MulAction.orbitRel (rootsOfUnity 3 F) (CoveredSpherical F ζ hζ U))

def orbitMeasure (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    Measure (CentralOrbitQuotient F ζ hζ U) :=
  Measure.map (orbitProjection F ζ hζ U) (coveredMeasure F ζ hζ R U)

def coveredChartMeasure (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (V : Set (CoveredSpherical F ζ hζ U)) : Measure V :=
  (coveredMeasure F ζ hζ R U).comap Subtype.val

def sphericalChartMeasure (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (V : Set (KPMsFixedHaarDisintegration.Spherical F ζ hζ U)) : Measure V :=
  (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).comap Subtype.val

theorem commuting_square
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    q F ζ hζ U ∘ piTilde F ζ hζ U = P.projection U := by
  funext x
  obtain ⟨g, rfl⟩ := Quotient.mk_surjective x
  obtain ⟨e, he⟩ :=
    KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_product_splitting
      F ζ hζ
  obtain ⟨p, hp⟩ : ∃ p : KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ p.1 * (p.2 : ActualCover F ζ hζ) = g :=
    ⟨e.symm g, by rw [← he (e.symm g).1 (e.symm g).2]; exact e.apply_symm_apply g⟩
  rw [← hp]
  simp only [Function.comp_apply]
  change q F ζ hζ U (piTilde F ζ hζ U
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ p.1 * (p.2 : ActualCover F ζ hζ)))) =
    P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ p.1 * (p.2 : ActualCover F ζ hζ)))
  rw [KPContSectorQuotientRelationsComparison.piTilde_quotientMap F ζ hζ U p.1 p.2,
    P.formula U p.1 p.2]
  exact KPContSectorCoveredQuotientVocabulary.q_mk F ζ hζ U _ p.2

theorem map_q_coveredMeasure
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    Measure.map (q F ζ hζ U) (coveredMeasure F ζ hζ R U) =
      KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U := by
  rw [coveredMeasure, KPMsFixedHaarDisintegration.sphericalMeasure]
  rw [Measure.map_map
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable
    (KPContSectorQuotientRelationsComparison.piTilde_continuous F ζ hζ U).measurable]
  rw [commuting_square F ζ hζ P U]

structure LevelSupport (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) : Prop where
  square : q F ζ hζ U ∘ piTilde F ζ hζ U = P.projection U
  pushforward : Measure.map (q F ζ hζ U) (coveredMeasure F ζ hζ R U) =
    KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U
  covered_open_positive : (coveredMeasure F ζ hζ R U).IsOpenPosMeasure
  spherical_open_positive :
    (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).IsOpenPosMeasure
  orbit_measure_preserving : MeasurePreserving (centralOrbitHomeomorph F ζ hζ U)
    (orbitMeasure F ζ hζ R U)
    (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U)
  covered_chart_open_positive : ∀ (V : Set (CoveredSpherical F ζ hζ U)),
    IsOpen V → (coveredChartMeasure F ζ hζ R U V).IsOpenPosMeasure
  spherical_chart_open_positive :
    ∀ (V : Set (KPMsFixedHaarDisintegration.Spherical F ζ hζ U)),
      IsOpen V → (sphericalChartMeasure F ζ hζ R P U V).IsOpenPosMeasure
  covered_relatively_open_positive : ∀ (V : Set (CoveredSpherical F ζ hζ U)),
    IsOpen V → ∀ (W : Set V), IsOpen W → W.Nonempty →
      0 < coveredChartMeasure F ζ hζ R U V W
  spherical_relatively_open_positive :
    ∀ (V : Set (KPMsFixedHaarDisintegration.Spherical F ζ hζ U)),
      IsOpen V → ∀ (W : Set V), IsOpen W → W.Nonempty →
        0 < sphericalChartMeasure F ζ hζ R P U V W

theorem levelSupport
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (hR : R.quotientHaar.IsOpenPosMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    LevelSupport F ζ hζ R P U := by
  have hcov : (coveredMeasure F ζ hζ R U).IsOpenPosMeasure := by
    haveI := hR
    exact Continuous.isOpenPosMeasure_map
      (KPContSectorQuotientRelationsComparison.piTilde_continuous F ζ hζ U)
      (KPContSectorQuotientRelationsComparison.piTilde_surjective F ζ hζ U)
  have hcovmap := map_q_coveredMeasure F ζ hζ R P U
  have hsph : (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).IsOpenPosMeasure := by
    rw [← hcovmap]
    haveI := hcov
    exact Continuous.isOpenPosMeasure_map
      (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U)
      (KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U)
  have hcovChart : ∀ V : Set (CoveredSpherical F ζ hζ U), IsOpen V →
      (coveredChartMeasure F ζ hζ R U V).IsOpenPosMeasure := by
    intro V hV
    haveI := hcov
    exact Measure.IsOpenPosMeasure.comap (coveredMeasure F ζ hζ R U) hV.isOpenEmbedding_subtypeVal
  have hsphChart : ∀ V : Set (KPMsFixedHaarDisintegration.Spherical F ζ hζ U), IsOpen V →
      (sphericalChartMeasure F ζ hζ R P U V).IsOpenPosMeasure := by
    intro V hV
    haveI := hsph
    exact Measure.IsOpenPosMeasure.comap
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) hV.isOpenEmbedding_subtypeVal
  refine ⟨commuting_square F ζ hζ P U, hcovmap, hcov, hsph, ?_, hcovChart, hsphChart, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact (KPContSectorQuotientRelationsComparison.centralOrbitHomeomorph F ζ hζ U).continuous.measurable
    · have hg : Measurable (KPContSectorQuotientRelationsComparison.centralOrbitHomeomorph
          F ζ hζ U) :=
        (KPContSectorQuotientRelationsComparison.centralOrbitHomeomorph F ζ hζ U).continuous.measurable
      have hf : Measurable (orbitProjection F ζ hζ U) :=
        (continuous_quotient_mk' (s := MulAction.orbitRel (rootsOfUnity 3 F)
          (CoveredSpherical F ζ hζ U))).measurable
      rw [orbitMeasure, Measure.map_map hg hf]
      rw [show (KPContSectorQuotientRelationsComparison.centralOrbitHomeomorph F ζ hζ U) ∘
          orbitProjection F ζ hζ U = q F ζ hζ U from
        funext (KPContSectorQuotientRelationsComparison.centralOrbitHomeomorph_mk F ζ hζ U)]
      exact hcovmap
  · intro V hV W hW hne
    haveI := hcovChart V hV
    exact hW.measure_pos _ hne
  · intro V hV W hW hne
    haveI := hsphChart V hV
    exact hW.measure_pos _ hne

end DedekindZetaZeroFree.KPContSectorFixedPushforwardSupport

namespace DedekindZetaZeroFree

end DedekindZetaZeroFree

end
