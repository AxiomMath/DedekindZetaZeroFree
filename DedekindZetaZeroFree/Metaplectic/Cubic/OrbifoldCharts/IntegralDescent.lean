module

public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.BorelDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContCotangentChartDescentIntegrals

open KPContActualCotangentCountableShrinking KPContCotangentFiniteQuotientBorel

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def baseMeasure (C : ShrunkChart F ζ hζ U R P H) : Measure C.baseDomain :=
  Measure.comap (Subtype.val : C.baseDomain → KPFiniteCuspAtlas.rawXU F ζ hζ U)
    ((KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict C.baseDomain)

variable {F ζ hζ U R P H}

def NonnegativeDescentIdentities (C : ShrunkChart F ζ hζ U R P H)
    (f : C.domain → ℝ≥0∞) (fbar : C.baseDomain → ℝ≥0∞) : Prop :=
  (∫⁻ x, f x ∂C.liftedMeasure) =
      (∫⁻ b, fbar b ∂baseMeasure F ζ hζ U R P H C) ∧
    ∀ E : Set C.baseDomain, MeasurableSet E →
      (∫⁻ x, f x ∂(C.liftedMeasure.restrict (C.quotientMap ⁻¹' E))) =
        (∫⁻ b, fbar b ∂((baseMeasure F ζ hζ U R P H C).restrict E))

def ComplexDescentIdentities (C : ShrunkChart F ζ hζ U R P H)
    (f : C.domain → ℂ) (fbar : C.baseDomain → ℂ) : Prop :=
  (Integrable f C.liftedMeasure ↔ Integrable fbar (baseMeasure F ζ hζ U R P H C)) ∧
    ((Integrable f C.liftedMeasure ∨ Integrable fbar (baseMeasure F ζ hζ U R P H C)) →
      (∫ x, f x ∂C.liftedMeasure) = (∫ b, fbar b ∂baseMeasure F ζ hζ U R P H C)) ∧
    ∀ E : Set C.baseDomain, MeasurableSet E →
      (Integrable f (C.liftedMeasure.restrict (C.quotientMap ⁻¹' E)) ↔
        Integrable fbar ((baseMeasure F ζ hζ U R P H C).restrict E)) ∧
      ((Integrable f (C.liftedMeasure.restrict (C.quotientMap ⁻¹' E)) ∨
        Integrable fbar ((baseMeasure F ζ hζ U R P H C).restrict E)) →
        (∫ x, f x ∂(C.liftedMeasure.restrict (C.quotientMap ⁻¹' E))) =
          (∫ b, fbar b ∂((baseMeasure F ζ hζ U R P H C).restrict E)))

private theorem shrunk_descends {C : ShrunkChart F ζ hζ U R P H} {S : Type*}
    [MeasurableSpace S] (f : C.domain → S) (hf : Measurable f)
    (hinv : ∀ σ y, f (C.action σ y) = f y) :
    BorelDescends C.quotientMap f :=
  shrunk_chart_borel_descent F ζ hζ U R P H C f hf hinv

theorem chart_pushforward (C : ShrunkChart F ζ hζ U R P H) :
    Measurable C.quotientMap ∧
      Measure.map C.quotientMap C.liftedMeasure = baseMeasure F ζ hζ U R P H C := by
  have h := every_shrunkChart_properties F ζ hζ U R P H C
  have hq : Measurable C.quotientMap :=
    h.measurable.subtype_mk (h := fun y => Set.mem_range_self y)
  refine ⟨hq, ?_⟩
  have hemb : MeasurableEmbedding
      (Subtype.val : C.baseDomain → KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
    MeasurableEmbedding.subtype_coe h.base_measurable
  have hval : Measure.map Subtype.val (baseMeasure F ζ hζ U R P H C) =
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict
        C.baseDomain := by
    rw [show baseMeasure F ζ hζ U R P H C = Measure.comap Subtype.val
      ((KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict
        C.baseDomain) from rfl]
    rw [map_comap_subtype_coe h.base_measurable,
      Measure.restrict_restrict_of_subset (subset_refl C.baseDomain)]
  apply MeasurableEmbedding.map_injective hemb
  rw [Measure.map_map hemb.measurable hq]
  rw [show (Subtype.val ∘ C.quotientMap) = C.toBase from rfl]
  rw [h.exact_pushforward, hval]

theorem chart_restricted_pushforward (C : ShrunkChart F ζ hζ U R P H)
    (E : Set C.baseDomain) (hE : MeasurableSet E) :
    Measure.map C.quotientMap (C.liftedMeasure.restrict (C.quotientMap ⁻¹' E)) =
      (baseMeasure F ζ hζ U R P H C).restrict E := by
  rw [← (chart_pushforward C).2]
  exact (Measure.restrict_map (chart_pushforward C).1 hE).symm

theorem chart_lintegral_descent (C : ShrunkChart F ζ hζ U R P H)
    (f : C.domain → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ σ y, f (C.action σ y) = f y)
    (fbar : C.baseDomain → ℝ≥0∞) (hbar : Measurable fbar)
    (hdesc : ∀ y, fbar (C.quotientMap y) = f y) :
    NonnegativeDescentIdentities C f fbar := by
  have hq := (chart_pushforward C).1
  have hmap := (chart_pushforward C).2
  refine ⟨?_, ?_⟩
  · rw [← hmap]
    exact ((lintegral_map hbar hq).trans (lintegral_congr fun y => hdesc y)).symm
  · intro E hE
    rw [← chart_restricted_pushforward C E hE]
    exact ((lintegral_map hbar hq).trans (lintegral_congr fun y => hdesc y)).symm

theorem chart_complex_descent (C : ShrunkChart F ζ hζ U R P H)
    (f : C.domain → ℂ) (hf : Measurable f)
    (hinv : ∀ σ y, f (C.action σ y) = f y)
    (fbar : C.baseDomain → ℂ) (hbar : Measurable fbar)
    (hdesc : ∀ y, fbar (C.quotientMap y) = f y) :
    ComplexDescentIdentities C f fbar := by
  have hq := (chart_pushforward C).1
  have hmap := (chart_pushforward C).2
  have hsm : AEStronglyMeasurable fbar
      (Measure.map C.quotientMap C.liftedMeasure) := hbar.aestronglyMeasurable
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmap, integrable_map_measure hbar.aestronglyMeasurable hq.aemeasurable]
    exact integrable_congr (Filter.Eventually.of_forall fun y => (hdesc y).symm)
  · intro _
    rw [← hmap, integral_map hq.aemeasurable hsm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => (hdesc y).symm)
  · intro E hE
    have hmapE := chart_restricted_pushforward C E hE
    refine ⟨?_, fun _ => ?_⟩
    · rw [← hmapE, integrable_map_measure hbar.aestronglyMeasurable hq.aemeasurable]
      exact integrable_congr (Filter.Eventually.of_forall fun y => (hdesc y).symm)
    · rw [← hmapE, integral_map hq.aemeasurable hbar.aestronglyMeasurable]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => (hdesc y).symm)

structure ChartDescentIntegrals (C : ShrunkChart F ζ hζ U R P H) : Prop where
  measurable : Measurable C.quotientMap
  exact_pushforward : Measure.map C.quotientMap C.liftedMeasure =
    baseMeasure F ζ hζ U R P H C
  restricted_pushforward : ∀ E : Set C.baseDomain, MeasurableSet E →
    Measure.map C.quotientMap (C.liftedMeasure.restrict (C.quotientMap ⁻¹' E)) =
      (baseMeasure F ζ hζ U R P H C).restrict E
  nonnegative : ∀ (f : C.domain → ℝ≥0∞), Measurable f →
    (∀ σ y, f (C.action σ y) = f y) →
    BorelDescends C.quotientMap f ∧
      ∀ fbar : C.baseDomain → ℝ≥0∞, Measurable fbar →
        (∀ y, fbar (C.quotientMap y) = f y) → NonnegativeDescentIdentities C f fbar
  complex : ∀ (f : C.domain → ℂ), Measurable f →
    (∀ σ y, f (C.action σ y) = f y) →
    BorelDescends C.quotientMap f ∧
      ∀ fbar : C.baseDomain → ℂ, Measurable fbar →
        (∀ y, fbar (C.quotientMap y) = f y) → ComplexDescentIdentities C f fbar

theorem chartDescentIntegrals (C : ShrunkChart F ζ hζ U R P H) :
    ChartDescentIntegrals C := by
  have hp := chart_pushforward C
  refine ⟨hp.1, hp.2, ?_, ?_, ?_⟩
  · intro E hE
    exact chart_restricted_pushforward C E hE
  · intro f hf hinv
    exact ⟨shrunk_descends f hf hinv, fun fbar hbar hdesc =>
      chart_lintegral_descent C f hf hinv fbar hbar hdesc⟩
  · intro f hf hinv
    exact ⟨shrunk_descends f hf hinv, fun fbar hbar hdesc =>
      chart_complex_descent C f hf hinv fbar hbar hdesc⟩

end DedekindZetaZeroFree.KPContCotangentChartDescentIntegrals

namespace DedekindZetaZeroFree

theorem kp_cont_cotangent_chart_descent_integrals
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :
    ∀ C : KPContActualCotangentCountableShrinking.ShrunkChart F ζ hζ U R P H,
      KPContCotangentChartDescentIntegrals.ChartDescentIntegrals C := by
  intro C
  exact KPContCotangentChartDescentIntegrals.chartDescentIntegrals C

end DedekindZetaZeroFree

end
