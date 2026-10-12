module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspCutoffBoundaryVanishing
public import DedekindZetaZeroFree.Geometry.Cusps.EmbeddedEndsAndCompactCollars
public import DedekindZetaZeroFree.Metaplectic.Cubic.Haar.SphericalSectorRealization

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCollarBuffer

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

abbrev Base := KPFiniteCuspAtlas.rawXU F ζ hζ U

abbrev Covered := KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ U

abbrev CuspIndex := Σ i : Fin (H.atlas U).componentCount,
  Fin ((H.atlas U).cuspAtlas i).cuspCount

abbrev Stabilizer (a : CuspIndex F ζ hζ U R P H) :=
  KPCuspArithmetic.conjugatedStabilizer F
    (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.1))
    (((H.atlas U).cuspAtlas a.1).cusp a.2)
    (((H.atlas U).cuspAtlas a.1).representative a.2)

def chartLift (a : CuspIndex F ζ hζ U R P H)
    (z : KPCuspCharts.Coordinates F) : Base F ζ hζ U :=
  Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
    ((((H.atlas U).cuspAtlas a.1).representative a.2 • KPCuspCharts.toArch F z),
      (H.atlas U).representative a.1)

def endSet (τ : ℝ) (a : CuspIndex F ζ hζ U R P H) : Set (Base F ζ hζ U) :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.1) ''
    KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.1))
      (((H.atlas U).cuspAtlas a.1).representative a.2) τ

def endChart (τ : ℝ) (a : CuspIndex F ζ hζ U R P H) :
    KPCuspCharts.HighQuotient F (Stabilizer F ζ hζ U R P H a) τ → Base F ζ hζ U :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.1) ∘
    KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.1))
      (((H.atlas U).cuspAtlas a.1).cusp a.2)
      (((H.atlas U).cuspAtlas a.1).representative a.2) τ

def height (τ : ℝ) (a : CuspIndex F ζ hζ U R P H)
    (x : Base F ζ hζ U) : ℝ :=
  if h : ∃ z : KPCuspCharts.Coordinates F,
      τ < z.2 ∧ chartLift F ζ hζ U R P H a z = x
  then (Classical.choose h).2 else 0

def zeroExtension (τ : ℝ) (a : CuspIndex F ζ hζ U R P H)
    (f : ℝ → ℝ) : Base F ζ hζ U → ℝ :=
  (endSet F ζ hζ U R P H τ a).indicator
    (fun x => f (height F ζ hζ U R P H τ a x))

def collars (τ T : ℝ) : Set (Base F ζ hζ U) :=
  KPCutoffSource.closedCollars (endSet F ζ hζ U R P H τ)
    (height F ζ hζ U R P H τ) T

def coveredCollars (τ T : ℝ) : Set (Covered F ζ hζ U) :=
  KPContSectorCoveredQuotientVocabulary.q F ζ hζ U ⁻¹' collars F ζ hζ U R P H τ T

structure CollarBuffer (T : ℝ) where
  τ : ℝ
  chart_threshold_le : (H.atlas U).threshold ≤ τ
  below_cutoff : τ < T
  dimension_formula : KPCuspLogShape.dimension F = Module.finrank ℚ F / 2
  positive_dimension : 0 < KPCuspLogShape.dimension F
  open_ends : ∀ a, IsOpen (endSet F ζ hζ U R P H τ a)
  disjoint_ends : Pairwise (fun a b => Disjoint
    (endSet F ζ hζ U R P H τ a) (endSet F ζ hζ U R P H τ b))
  chart_embedding : ∀ a, Topology.IsEmbedding (endChart F ζ hζ U R P H τ a)
  chart_range : ∀ a, Set.range (endChart F ζ hζ U R P H τ a) =
    endSet F ζ hζ U R P H τ a
  lift_range : ∀ a, chartLift F ζ hζ U R P H a ''
    {z : KPCuspCharts.Coordinates F | τ < z.2} = endSet F ζ hζ U R P H τ a

  height_coordinates : ∀ a (z : KPCuspCharts.Coordinates F), τ < z.2 →
    height F ζ hζ U R P H τ a (chartLift F ζ hζ U R P H a z) = z.2
  height_continuous : ∀ a,
    ContinuousOn (height F ζ hζ U R P H τ a) (endSet F ζ hζ U R P H τ a)
  height_smooth : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞)
    (fun z : KPCuspCharts.Coordinates F =>
      height F ζ hζ U R P H τ a (chartLift F ζ hζ U R P H a z))
    {z | τ < z.2}

  height_stabilizer : ∀ a (g : Stabilizer F ζ hζ U R P H a)
      (z : KPCuspCharts.Coordinates F), τ < z.2 →
    height F ζ hζ U R P H τ a (chartLift F ζ hζ U R P H a
      ((((H.atlas U).cuspAtlas a.1).geometry a.2).crossAction g z.1, z.2)) =
      height F ζ hζ U R P H τ a (chartLift F ζ hζ U R P H a z)

  height_transitions : ∀ a (g : Stabilizer F ζ hζ U R P H a)
      (A : Matrix.GeneralLinearGroup (Fin 2) F),
    Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
    ∀ (z : KPCuspCharts.Coordinates F), τ < z.2 →
      let D := ((H.atlas U).cuspAtlas a.1).parabolic a.2
      let z' := KPCuspCharts.affine F H.totallyComplex D.E D.integralUnits
        (D.ratio g) (A 0 1 / A 1 1) z
      chartLift F ζ hζ U R P H a z' = chartLift F ζ hζ U R P H a z ∧
      height F ζ hζ U R P H τ a (chartLift F ζ hζ U R P H a z') =
        height F ζ hζ U R P H τ a (chartLift F ζ hζ U R P H a z)
  compact_each_collar : ∀ a, IsCompact (closure
    {x | x ∈ endSet F ζ hζ U R P H τ a ∧
      height F ζ hζ U R P H τ a x ∈ Set.Icc T (T + 1)})
  collar_in_chart_interior : ∀ a, closure
    {x | x ∈ endSet F ζ hζ U R P H τ a ∧
      height F ζ hζ U R P H τ a x ∈ Set.Icc T (T + 1)} ⊆
        interior (endSet F ζ hζ U R P H τ a)
  compact_collars : IsCompact (collars F ζ hζ U R P H τ T)
  compact_covered_collars : IsCompact (coveredCollars F ζ hζ U R P H τ T)
  finite_covered_measure :
    KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U
      (coveredCollars F ζ hζ U R P H τ T) < (⊤ : ℝ≥0∞)

  boundary_height_buffer : ∀ a x, x ∈ frontier (endSet F ζ hζ U R P H τ a) →
    ∃ V : Set (Base F ζ hζ U), IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, y ∈ endSet F ζ hζ U R P H τ a →
        height F ζ hζ U R P H τ a y < T

  boundary_zero_extension : ∀ a x,
    x ∈ frontier (endSet F ζ hζ U R P H τ a) →
    ∃ V : Set (Base F ζ hζ U), IsOpen V ∧ x ∈ V ∧
      ∀ (χ : KPCutoffSource.SmoothCuspCutoff T) y, y ∈ V →
        zeroExtension F ζ hζ U R P H τ a χ.toFun y = 0 ∧
        zeroExtension F ζ hζ U R P H τ a (deriv χ.toFun) y = 0 ∧
        zeroExtension F ζ hζ U R P H τ a (deriv (deriv χ.toFun)) y = 0

end DedekindZetaZeroFree.KPContActualCollarBuffer

namespace DedekindZetaZeroFree

theorem kp_cont_actual_collar_buffer
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (_hR : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (T : ℝ) (hT : (H.atlas U).threshold < T) :
    Nonempty (KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H T) := by
  let τ := ((H.atlas U).threshold + T) / 2
  have hτ : (H.atlas U).threshold ≤ τ := by dsimp [τ]; linarith
  have hτT : τ < T := by dsimp [τ]; linarith
  obtain ⟨hlift, hcoord, hcont, hsmooth, hstab, htrans⟩ :=
    KPActualCollarBuffer.actual_height_descent F ζ hζ H.totallyComplex U
      (H.atlas U) τ hτ
  obtain ⟨hopen, hdisj, hemb, hrange, heach, hinterior, hcompact⟩ :=
    KPActualCollarBuffer.actual_end_charts_compact_collars F ζ hζ
      H.totallyComplex U (H.atlas U) τ T hτ hτT
  obtain ⟨hbuffer, hzero⟩ :=
    KPActualCollarBuffer.actual_boundary_zero_buffer F ζ hζ
      H.totallyComplex U (H.atlas U) τ T hτ hτT
  have hc : IsCompact (KPContActualCollarBuffer.collars F ζ hζ U R P H τ T) := by
    exact hcompact
  have hcovered : IsCompact
      (KPContActualCollarBuffer.coveredCollars F ζ hζ U R P H τ T) :=
    (KPContSectorSmoothFramesSupport.q_closed_and_proper F ζ hζ U).2 _ hc
  have hmeasure : KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U
      (KPContActualCollarBuffer.coveredCollars F ζ hζ U R P H τ T) < (⊤ : ℝ≥0∞) := by
    letI := KPContSectorFixedMeasureLocalFiniteness.coveredMeasure_finiteOnCompacts
      F ζ hζ R U
    exact hcovered.measure_lt_top
  have hdim : KPCuspLogShape.dimension F = Module.finrank ℚ F / 2 :=
    (kp_cont_finite_cusp_atlas F ζ hζ U).choose_spec.1
  refine ⟨{ τ := τ
            chart_threshold_le := hτ
            below_cutoff := hτT
            dimension_formula := hdim
            positive_dimension := KPCuspCharts.positive_dimension F H.totallyComplex
            open_ends := ?_
            disjoint_ends := ?_
            chart_embedding := ?_
            chart_range := ?_
            lift_range := ?_
            height_coordinates := ?_
            height_continuous := ?_
            height_smooth := ?_
            height_stabilizer := ?_
            height_transitions := ?_
            compact_each_collar := ?_
            collar_in_chart_interior := ?_
            compact_collars := hc
            compact_covered_collars := hcovered
            finite_covered_measure := hmeasure
            boundary_height_buffer := ?_
            boundary_zero_extension := ?_ }⟩
  all_goals
    dsimp only [KPContActualCollarBuffer.zeroExtension, KPContActualCollarBuffer.height,
      KPContActualCollarBuffer.chartLift, KPContActualCollarBuffer.endSet,
      KPContActualCollarBuffer.endChart]
  · exact hopen
  · exact hdisj
  · exact hemb
  · exact hrange
  · exact hlift
  · exact hcoord
  · exact hcont
  · exact hsmooth
  · exact hstab
  · exact htrans
  · exact heach
  · exact hinterior
  · exact hbuffer
  · exact hzero

end DedekindZetaZeroFree

end
