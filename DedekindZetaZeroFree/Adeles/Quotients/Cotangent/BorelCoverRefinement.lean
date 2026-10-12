module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.CountableShrinkingCharts

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentBorelRefinement

open KPContActualCotangentCountableShrinking

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (C : CountableCover F ζ hζ U R P H)

def basePiece (n : ℕ) : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  disjointed (fun k => (C.chart k).baseDomain) n

def liftedPiece (n : ℕ) : Set (C.chart n).domain :=
  (C.chart n).toBase ⁻¹' basePiece C n

structure Properties : Prop where
  base_measurable : ∀ n, MeasurableSet (basePiece C n)
  base_subset : ∀ n, basePiece C n ⊆ (C.chart n).baseDomain
  pairwise_disjoint : Pairwise (fun n m => Disjoint (basePiece C n) (basePiece C m))
  covers : (⋃ n, basePiece C n) = Set.univ
  lifted_measurable : ∀ n, MeasurableSet (liftedPiece C n)
  lifted_invariant : ∀ n (σ : (C.chart n).Isotropy),
    (C.chart n).action σ '' liftedPiece C n = liftedPiece C n
  exact_pushforward : ∀ n,
    Measure.map (C.chart n).toBase
        ((C.chart n).liftedMeasure.restrict (liftedPiece C n)) =
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict (basePiece C n)
  lintegral_eq_tsum : ∀ (h : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞),
    Measurable h →
      (∫⁻ x, h x ∂(KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U)) =
        ∑' n, ∫⁻ y in liftedPiece C n, h ((C.chart n).toBase y)
          ∂(C.chart n).liftedMeasure
  integrableOn_lifted : ∀ (h : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ),
    Integrable h (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) →
      ∀ n, IntegrableOn (fun y => h ((C.chart n).toBase y))
        (liftedPiece C n) (C.chart n).liftedMeasure
  summable_integrals : ∀ (h : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ),
    Integrable h (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) →
      Summable (fun n => ∫ y in liftedPiece C n, h ((C.chart n).toBase y)
        ∂(C.chart n).liftedMeasure)
  integral_eq_tsum : ∀ (h : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ),
    Integrable h (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) →
      (∫ x, h x ∂(KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U)) =
        ∑' n, ∫ y in liftedPiece C n, h ((C.chart n).toBase y)
          ∂(C.chart n).liftedMeasure

end DedekindZetaZeroFree.KPContActualCotangentBorelRefinement

namespace DedekindZetaZeroFree

open KPContActualCotangentBorelRefinement

theorem kp_cont_actual_cotangent_borel_refinement
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (C : KPContActualCotangentCountableShrinking.CountableCover F ζ hζ U R P H) :
    KPContActualCotangentBorelRefinement.Properties C := by
  classical
  let μ : Measure (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
    KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U
  have hbase : ∀ n, MeasurableSet (basePiece C n) := fun n =>
    MeasurableSet.disjointed (fun k => (C.properties k).base_measurable) n
  have hsub : ∀ n, basePiece C n ⊆ (C.chart n).baseDomain := fun n =>
    disjointed_subset (fun k => (C.chart k).baseDomain) n
  have hdisj : Pairwise (fun n m => Disjoint (basePiece C n) (basePiece C m)) := by
    simpa only [basePiece] using disjoint_disjointed (fun k => (C.chart k).baseDomain)
  have hcov : (⋃ n, basePiece C n) = Set.univ := by
    have h : (⋃ n, basePiece C n) = ⋃ n, (C.chart n).baseDomain := by
      simp only [basePiece, iUnion_disjointed]
    rw [h]; exact C.covers
  have htoBase_action : ∀ (n : ℕ) (σ : (C.chart n).Isotropy) (y : (C.chart n).domain),
      (C.chart n).toBase ((C.chart n).action σ y) = (C.chart n).toBase y := by
    intro n σ y
    exact (((C.properties n).orbit_fibers y ((C.chart n).action σ y)).mpr ⟨σ, rfl⟩).symm
  have haction_cancel : ∀ (n : ℕ) (σ : (C.chart n).Isotropy) (y : (C.chart n).domain),
      (C.chart n).action σ ((C.chart n).action σ⁻¹ y) = y := by
    intro n σ y
    apply Subtype.ext
    simp only [KPContActualCotangentCountableShrinking.ShrunkChart.action, Subtype.coe_mk]
    rw [← mul_smul]
    have h1 : (σ.val : KPCuspArithmetic.PGL2 F) * (σ⁻¹).val = 1 := by
      have h2 : ((σ * σ⁻¹ : (C.chart n).Isotropy) : KPCuspArithmetic.PGL2 F) = 1 := by
        rw [mul_inv_cancel]; simp
      simpa using h2
    rw [h1, one_smul]
  have hlmeas : ∀ n, MeasurableSet (liftedPiece C n) := fun n =>
    (C.properties n).measurable (hbase n)
  have hinv : ∀ n (σ : (C.chart n).Isotropy),
      (C.chart n).action σ '' liftedPiece C n = liftedPiece C n := by
    intro n σ
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      show (C.chart n).toBase ((C.chart n).action σ y) ∈ basePiece C n
      rw [htoBase_action n σ y]
      exact hy
    · intro y hy
      refine ⟨(C.chart n).action σ⁻¹ y, ?_, haction_cancel n σ y⟩
      show (C.chart n).toBase ((C.chart n).action σ⁻¹ y) ∈ basePiece C n
      rw [htoBase_action n σ⁻¹ y]
      exact hy
  have hexact : ∀ n,
      Measure.map (C.chart n).toBase ((C.chart n).liftedMeasure.restrict (liftedPiece C n)) =
        μ.restrict (basePiece C n) := by
    intro n
    rw [liftedPiece,
      ← Measure.restrict_map (C.properties n).measurable (hbase n),
      (C.properties n).exact_pushforward]
    rw [Measure.restrict_restrict (hbase n), Set.inter_eq_left.mpr (hsub n)]
  have hlin : ∀ (h : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞), Measurable h →
      (∫⁻ x, h x ∂μ) =
        ∑' n, ∫⁻ y in liftedPiece C n, h ((C.chart n).toBase y)
          ∂(C.chart n).liftedMeasure := by
    intro h hh
    have h1 : (∫⁻ x, h x ∂μ) = ∫⁻ x in ⋃ n, basePiece C n, h x ∂μ := by
      rw [hcov, Measure.restrict_univ]
    rw [h1, lintegral_iUnion (fun n => hbase n) hdisj h]
    refine tsum_congr fun n => ?_
    rw [← hexact n]
    exact lintegral_map hh (C.properties n).measurable
  have hterm : ∀ (h : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ), Integrable h μ → ∀ n,
      (∫ x in basePiece C n, h x ∂μ) =
        ∫ y in liftedPiece C n, h ((C.chart n).toBase y)
          ∂(C.chart n).liftedMeasure := by
    intro h hint n
    have hmap := hexact n
    have haesm : AEStronglyMeasurable h
        (Measure.map (C.chart n).toBase
          ((C.chart n).liftedMeasure.restrict (liftedPiece C n))) := by
      rw [hmap]; exact hint.integrableOn.aestronglyMeasurable
    rw [← hmap]
    exact integral_map (C.properties n).measurable.aemeasurable haesm
  have hint_lifted : ∀ (h : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ), Integrable h μ → ∀ n,
      IntegrableOn (fun y => h ((C.chart n).toBase y))
        (liftedPiece C n) (C.chart n).liftedMeasure := by
    intro h hint n
    have hmap := hexact n
    have hint' : Integrable h
        (Measure.map (C.chart n).toBase
          ((C.chart n).liftedMeasure.restrict (liftedPiece C n))) := by
      rw [hmap]; exact hint.integrableOn
    exact (integrable_map_measure hint'.aestronglyMeasurable
      (C.properties n).measurable.aemeasurable).mp hint'
  have hsum : ∀ (h : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ), Integrable h μ →
      Summable (fun n => ∫ y in liftedPiece C n, h ((C.chart n).toBase y)
        ∂(C.chart n).liftedMeasure) := by
    intro h hint
    have hhs := hasSum_integral_iUnion (μ := μ) (s := fun n => basePiece C n) (f := h)
      (fun n => hbase n) hdisj (by rw [hcov]; exact hint.integrableOn)
    simpa only [hterm h hint] using hhs.summable
  have hint_eq : ∀ (h : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ), Integrable h μ →
      (∫ x, h x ∂μ) =
        ∑' n, ∫ y in liftedPiece C n, h ((C.chart n).toBase y)
          ∂(C.chart n).liftedMeasure := by
    intro h hint
    have hhs := hasSum_integral_iUnion (μ := μ) (s := fun n => basePiece C n) (f := h)
      (fun n => hbase n) hdisj (by rw [hcov]; exact hint.integrableOn)
    have h1 : (∫ x, h x ∂μ) = ∫ x in ⋃ n, basePiece C n, h x ∂μ := by
      rw [hcov, Measure.restrict_univ]
    rw [h1, ← hhs.tsum_eq]
    exact tsum_congr fun n => hterm h hint n
  exact ⟨hbase, hsub, hdisj, hcov, hlmeas, hinv, hexact, hlin,
    hint_lifted, hsum, hint_eq⟩

end DedekindZetaZeroFree

end
