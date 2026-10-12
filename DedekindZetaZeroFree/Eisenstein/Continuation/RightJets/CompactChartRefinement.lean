module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Spherical.HolomorphicSmoothSectionGluing

@[expose] public section

noncomputable section
open scoped Classical NumberField
open Topology Filter

namespace DedekindZetaZeroFree.KPContActualRightCanonicalRefinement

open KPContLocalNorm KPContActualSphericalRightFieldIdentification
open KPContActualSmoothLineGluing KPContActualChartRestrictionDensity
open KPContSectorSmoothFramesSupport KPContSectorScalarLineAlgebra KPContSectorLineL2Isometry
open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

structure Piece where
  group : GroupChart F ζ hζ U R P H
  chart : KPContActualSmoothLineGluing.ChartBall F ζ hζ U R P H
  openSet : Set (Space (groupDimension F))
  isOpen : IsOpen openSet
  contained : openSet ⊆ group.T.carrier
  compact : Set (Space (groupDimension F))
  isCompact : IsCompact compact
  compact_inside : compact ⊆ openSet
  projection : Space (groupDimension F) → Space (KPCuspLogShape.dimension F * 3)
  projection_eq : projection = fun x => (KPContActualChartRestrictionDensity.coordinates F).symm
    (baseCoordinates F (group.π x))
  smooth_projection : ContDiffOn ℝ (⊤ : ℕ∞) projection openSet
  projection_inside : Set.MapsTo projection openSet chart.ball.carrier
  compact_projection : IsCompact (projection '' compact)
  fields_smooth : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (group.fields i) openSet
  base_formula : ∀ x ∈ openSet,
    KPContSectorCoveredQuotientVocabulary.q F ζ hζ U
      (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (group.groupLift x))) =
      KPContActualChartRestrictionDensity.basePoint F ζ hζ U R P H chart.component (projection x)
  scalar_formula : ∀ u : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H,
    ∀ x ∈ openSet,
      (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H u).val
        (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U
          (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (group.groupLift x))) =
        KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u chart (projection x)
  piece_compact : IsCompact (group.piece compact)
  local_word : ∀ f : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ → ℂ,
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (group.groupLift x)) openSet →
      ∀ w, ∀ x ∈ openSet,
        actualRightWord F ζ hζ w f (group.groupLift x) =
          KPContRightJets.rightWord group.fields w (fun y => f (group.groupLift y)) x

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

 def canonicalProjection (D : GroupChart F ζ hζ U R P H) :
    Space (groupDimension F) → Space (KPCuspLogShape.dimension F * 3) :=
  fun x => (coordinates F).symm (baseCoordinates F (D.π x))
private lemma canonicalProjection_smooth (D : GroupChart F ζ hζ U R P H) :
    ContDiffOn ℝ (⊤ : ℕ∞) (canonicalProjection D) D.T.carrier :=
  (CoreChartLocalizers.CutoffConstruction.ChartDensityConstruction.coordinates_symm_contDiff
    (KPCuspLogShape.dimension F)).comp_contDiffOn ((baseCoordinates F).contDiff.comp_contDiffOn D.π_smooth)
private lemma canonicalProjection_zero (D : GroupChart F ζ hζ U R P H) :
    canonicalProjection D 0 = (coordinates F).symm D.baseCenter := by
  unfold canonicalProjection GroupChart.π
  rw [ContinuousLinearEquiv.apply_symm_apply, map_zero,
    D.exponential.exponential_formula _ D.exponential.zero_mem]
  have he : KPSmoothLocalQuotientCharts.matrixExp F 0 = 1 := by
    letI := actualLieChartedSpace F
    letI := actualLieGroup F
    simpa only [actualLieData_exponential] using (actualLieData F).exponential_zero
  rw [he, mul_one, ← D.baseCenter_actual]

 def shrink (D : GroupChart F ζ hζ U R P H)
    (T : LocalBall (groupDimension F)) (h0 : (0 : Space (groupDimension F)) ∈ T.carrier)
    (hT : closure T.carrier ⊆ D.T.carrier) : GroupChart F ζ hζ U R P H :=
  { D with
    T := T
    zero_mem := h0
    closure_source := fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hy
      exact D.closure_source ⟨x, subset_closure (hT hx), rfl⟩
    image_inside := fun x hx => D.image_inside x (subset_closure (hT hx)) }

private lemma local_piece (D : GroupChart F ζ hζ U R P H) :
    ∃ p : Piece (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H),
      p.group.groupLift 0 = D.groupLift 0 ∧ p.group.piece p.compact ∈ 𝓝 (D.groupLift 0) := by
  let A := canonicalChartBall F ζ hζ U R P H D.component D.baseCenter (phaseClass F ζ hζ U D.phase)
  have hproj0 : canonicalProjection D 0 ∈ A.ball.carrier := by
    rw [canonicalProjection_zero]
    exact canonicalBall_mem F ζ hζ U R P H D.component D.baseCenter
  have hnh : D.T.carrier ∩ canonicalProjection D ⁻¹' A.ball.carrier ∈ 𝓝 (0 : Space (groupDimension F)) := by
    apply inter_mem (Metric.isOpen_ball.mem_nhds D.zero_mem)
    exact ((canonicalProjection_smooth D).continuousOn.continuousAt
      (Metric.isOpen_ball.mem_nhds D.zero_mem)).preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds hproj0)
  obtain ⟨r, hr, hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnh
  let T : LocalBall (groupDimension F) := ⟨D.T.dimension_pos, 0, r, hr⟩
  have hT : closure T.carrier ⊆ D.T.carrier := by
    rw [LocalBall.carrier, closure_ball _ hr.ne']
    exact fun x hx => (hrV hx).1
  let E := shrink D T (Metric.mem_ball_self hr) hT
  obtain ⟨K, hK, hKT, hpK, hKn⟩ := E.compact_piece_nhds
  have hinside : Set.MapsTo (canonicalProjection E) E.T.carrier A.ball.carrier := by
    intro x hx
    exact (hrV (Metric.ball_subset_closedBall hx)).2
  refine ⟨{
    group := E
    chart := A
    openSet := E.T.carrier
    isOpen := Metric.isOpen_ball
    contained := Set.Subset.rfl
    compact := K
    isCompact := hK
    compact_inside := hKT
    projection := canonicalProjection E
    projection_eq := rfl
    smooth_projection := canonicalProjection_smooth E
    projection_inside := hinside
    compact_projection := hK.image_of_continuousOn ((canonicalProjection_smooth E).continuousOn.mono hKT)
    fields_smooth := E.fields_smooth_actual
    base_formula := ?_
    scalar_formula := ?_
    piece_compact := hpK
    local_word := E.identification.right_iteration }, rfl, hKn⟩
  · intro x hx
    rw [E.actual_base_chart x hx, coveredChart_mk, ← z_mk, q_z, q_mk]
    simp only [basePoint, canonicalProjection, Homeomorph.apply_symm_apply]
    exact ((H.atlas U).components_formula E.component (Quotient.mk _ (baseCoordinates F (E.π x)))).symm
  · intro u x hx
    rw [E.global_scalar_pullback _ x hx]
    simp only [coefficient, A, canonicalChartBall, frameCoefficient_class,
      scalarRepresentative_eq_symm, LinearEquiv.apply_symm_apply,
      KPContRightJets.scalarLift, GroupChart.frame, canonicalProjection, Homeomorph.apply_symm_apply]
    rfl

theorem compact_refinement
    (actual : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (C : Set (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)) (hC : IsCompact C) :
    ∃ n : ℕ, ∃ p : Fin n → Piece (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H),
      C ⊆ ⋃ j, (p j).group.piece (p j).compact := by
  choose D hD using chart_at_point F ζ hζ U R P H
  choose p hp hn using (fun g => local_piece (D g))
  obtain ⟨S, _, hS⟩ := hC.elim_nhds_subcover (fun g => (p g).group.piece (p g).compact)
    (fun g _ => by simpa only [hD] using hn g)
  let e : Fin S.card ≃ S := S.equivFin.symm
  refine ⟨S.card, fun j => p (e j).val, ?_⟩
  intro g hg
  obtain ⟨x, hx, hgx⟩ := Set.mem_iUnion₂.mp (hS hg)
  obtain ⟨j, hj⟩ := e.surjective ⟨x, hx⟩
  exact Set.mem_iUnion.mpr ⟨j, by simpa only [hj] using hgx⟩

end DedekindZetaZeroFree.KPContActualRightCanonicalRefinement

end
