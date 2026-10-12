module

public import DedekindZetaZeroFree.Adeles.Quotients.LineSections.CompactL2ZeroExtension
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.ChartJetHolomorphy
public import DedekindZetaZeroFree.Metaplectic.Cubic.Cotangent.GenuineTwistAndIsotropy

@[expose] public section

noncomputable section
open scoped Classical NumberField
open Topology

namespace DedekindZetaZeroFree.CompactChartRestriction

open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

local notation "V" => KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U
local notation "X" => KPContLocalNorm.Space (KPContActualCutoffChartJetHolomorphy.dimension F)

def chartPoint {i} (q : KPContActualCutoffChartJetHolomorphy.Chart F ζ hζ C R P H U i)
    (x : X) : CoveredSpherical F ζ hζ V :=
  Quotient.mk (coveredRelation F ζ hζ V)
    (q.kind.representative • KPContCotangentActualOverlap.labeledA q.places
      (KPContActualCutoffChartJetHolomorphy.coordinates F x), (H.atlas V).representative i)

variable (L : KPContActualCompactSectorL2Map.CompactDomain F ζ hζ
  (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R)

structure FiniteChartCover where
  count : ℕ
  component : Fin count → Fin (H.atlas V).componentCount
  chart : ∀ j, KPContActualCutoffChartJetHolomorphy.Chart F ζ hζ C R P H U (component j)
  outer : Fin count → TopologicalSpace.Compacts X
  outer_contained : ∀ j, (outer j : Set X) ⊆
    KPContActualCutoffChartJetHolomorphy.chartDomain F ζ hζ C R P H U (chart j)
  piece : Fin count → TopologicalSpace.Compacts X
  piece_eq : ∀ j, (piece j : Set X) = (outer j : Set X) ∩
    chartPoint F ζ hζ C R P H U (chart j) ⁻¹' (L.compact : Set (CoveredSpherical F ζ hζ V))
  projection : ∀ j, C(piece j, L.compact)
  projection_formula : ∀ j x, (projection j x).val =
    chartPoint F ζ hζ C R P H U (chart j) x.val
  phase : ∀ j, C(piece j, ℂ)
  phase_formula : ∀ j x, phase j x =
    (chi F ζ hζ ((chart j).splitting
      (KPContActualCutoffChartJetHolomorphy.coordinates F x.val)) : ℂ)
  covers : ∀ y : L.compact, ∃ (j : Fin count) (x : piece j) (ε : rootsOfUnity 3 F),
    y.val = z F ζ hζ V ε (projection j x).val

private theorem continuous_labeledA_of
    (places : Fin (KPContCotangentActualOverlap.d F) ≃ Fin (KPCuspLogShape.dimension F)) :
    Continuous (KPContCotangentActualOverlap.labeledA places) := by
  apply continuous_pi
  intro k
  exact (continuous_apply (places.symm k)).comp
    (CotangentLogCoframe.A (KPContCotangentActualOverlap.d F)).continuous

private theorem continuous_labeledAInv_of
    (places : Fin (KPContCotangentActualOverlap.d F) ≃ Fin (KPCuspLogShape.dimension F)) :
    Continuous (KPContCotangentActualOverlap.labeledAInv places) := by
  apply (CotangentLogCoframe.A (KPContCotangentActualOverlap.d F)).symm.continuous.comp
  apply continuous_pi
  intro k
  exact continuous_apply (places k)

private theorem labeledA_labeledAInv_of
    (places : Fin (KPContCotangentActualOverlap.d F) ≃ Fin (KPCuspLogShape.dimension F))
    (z : KPCuspGenuineMonodromy.SymmetricSpace F) :
    KPContCotangentActualOverlap.labeledA places
      (KPContCotangentActualOverlap.labeledAInv places z) = z := by
  funext k
  simp only [KPContCotangentActualOverlap.labeledA, KPContCotangentActualOverlap.labeledAInv,
    ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]

 def coordsInv (m : KPContCotangentActualOverlap.M F) : X :=
  WithLp.toLp 2 (fun j : Fin (KPContActualCutoffChartJetHolomorphy.dimension F) =>
    m (finProdFinEquiv.symm j))

private theorem continuous_coordsInv : Continuous (coordsInv F) := by
  unfold coordsInv
  fun_prop

private theorem continuous_coordinates :
    Continuous (KPContActualCutoffChartJetHolomorphy.coordinates F) := by
  unfold KPContActualCutoffChartJetHolomorphy.coordinates
  fun_prop

private theorem coordinates_coordsInv (m : KPContCotangentActualOverlap.M F) :
    KPContActualCutoffChartJetHolomorphy.coordinates F (coordsInv F m) = m := by
  apply PiLp.ext
  intro i
  simp only [coordsInv, KPContActualCutoffChartJetHolomorphy.coordinates,
    PiLp.toLp_apply, Equiv.symm_apply_apply]

private theorem continuous_chartPoint {i}
    (q : KPContActualCutoffChartJetHolomorphy.Chart F ζ hζ C R P H U i) :
    Continuous (chartPoint F ζ hζ C R P H U q) := by
  unfold chartPoint
  apply continuous_quotient_mk'.comp
  apply Continuous.prodMk
  · exact (KPCuspSiegel.continuous_action F q.kind.representative).comp
      ((continuous_labeledA_of F q.places).comp (continuous_coordinates F))
  · exact continuous_const

private theorem q_representative
    (i : Fin (H.atlas V).componentCount) (x : SymmetricSpace F) :
    q F ζ hζ V (Quotient.mk (coveredRelation F ζ hζ V)
        (x, (H.atlas V).representative i)) =
      KPFiniteCuspAtlas.componentMap F ζ hζ V ((H.atlas V).representative i)
        (KPCuspSiegel.projection F
          (KPCuspGenuineMonodromy.Component F ζ hζ V ((H.atlas V).representative i)) x) := by
  rw [q_mk]
  rfl

theorem finiteChartCover_exists
    (_realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ V R P H) :
    Nonempty (FiniteChartCover F ζ hζ C R P H U L) := by
  obtain ⟨-, ⟨cov⟩⟩ := kp_cont_actual_cotangent_countable_shrinking F ζ hζ V R P H
  have hK : IsCompact ((q F ζ hζ V) '' (L.compact : Set (CoveredSpherical F ζ hζ V))) :=
    L.compact.isCompact.image (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ V)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun n => (cov.chart n).baseDomain)
    (fun n => (cov.properties n).base_open) (by rw [cov.covers]; exact Set.subset_univ _)
  let e : Fin s.card ≃ {n // n ∈ s} := (Finset.equivFinOfCardEq (rfl : s.card = s.card)).symm
  let nOf : Fin s.card → ℕ := fun j => (e j).val
  have hnOf : ∀ j, nOf j ∈ s := fun j => (e j).property
  let places : Fin (KPContCotangentActualOverlap.d F) ≃ Fin (KPCuspLogShape.dimension F) :=
    KPContCotangentActualOverlap.placeEquiv F ζ hζ
  let component : Fin s.card → Fin (H.atlas V).componentCount :=
    fun j => (cov.chart (nOf j)).component
  let chart : ∀ j : Fin s.card,
      KPContActualCutoffChartJetHolomorphy.Chart F ζ hζ C R P H U (component j) := fun j =>
    { kind := KPContCotangentActualOverlap.ChartKind.orbifold
        (cov.chart (nOf j)).center (cov.chart (nOf j)).larger
      places := places
      splitting := fun _ => 1
      splitting_locallyConstant := IsLocallyConstant.const 1 }
  let outer : Fin s.card → TopologicalSpace.Compacts X := fun j =>
    ⟨coordsInv F '' (KPContCotangentActualOverlap.labeledAInv places ''
        closure (cov.chart (nOf j)).domain),
      ((cov.chart (nOf j)).closure_compact.image
        (continuous_labeledAInv_of F places)).image (continuous_coordsInv F)⟩
  have outer_contained : ∀ j, (outer j : Set X) ⊆
      KPContActualCutoffChartJetHolomorphy.chartDomain F ζ hζ C R P H U (chart j) := by
    intro j x hx
    obtain ⟨w', hw', rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hw'
    show KPContCotangentActualOverlap.labeledA places
      (KPContActualCutoffChartJetHolomorphy.coordinates F
        (coordsInv F (KPContCotangentActualOverlap.labeledAInv places w))) ∈
      (KPContCotangentActualOverlap.ChartKind.orbifold
        (cov.chart (nOf j)).center (cov.chart (nOf j)).larger).archDomain
    rw [coordinates_coordsInv, labeledA_labeledAInv_of]
    exact (cov.chart (nOf j)).closure_subset hw
  let piece : Fin s.card → TopologicalSpace.Compacts X := fun j =>
    ⟨(outer j : Set X) ∩ (chartPoint F ζ hζ C R P H U (chart j)) ⁻¹'
        (L.compact : Set (CoveredSpherical F ζ hζ V)),
      (outer j).isCompact.inter_right
        ((L.compact.isCompact.isClosed).preimage
          (continuous_chartPoint F ζ hζ C R P H U (chart j)))⟩
  let projection : ∀ j : Fin s.card, C(piece j, L.compact) := fun j =>
    { toFun := fun x => ⟨chartPoint F ζ hζ C R P H U (chart j) x.val, x.property.2⟩
      continuous_toFun := Continuous.subtype_mk
        ((continuous_chartPoint F ζ hζ C R P H U (chart j)).comp continuous_subtype_val)
        (fun x => x.property.2) }
  let phase : ∀ j : Fin s.card, C(piece j, ℂ) := fun j =>
    { toFun := fun x => (chi F ζ hζ ((chart j).splitting
        (KPContActualCutoffChartJetHolomorphy.coordinates F x.val)) : ℂ)
      continuous_toFun := by
        have hc : Continuous (fun x : piece j =>
            (⟨KPContActualCutoffChartJetHolomorphy.coordinates F x.val,
              outer_contained j x.property.1⟩ :
              {y : KPContCotangentActualOverlap.M F //
                KPContCotangentActualOverlap.labeledA places y ∈
                  (chart j).kind.archDomain})) :=
          Continuous.subtype_mk
            ((continuous_coordinates F).comp continuous_subtype_val) _
        exact ((((chart j).splitting_locallyConstant).comp_continuous hc).comp
          (fun ε : rootsOfUnity 3 F => (chi F ζ hζ ε : ℂ))).continuous }
  have covers : ∀ y : L.compact, ∃ (j : Fin s.card) (x : piece j) (ε : rootsOfUnity 3 F),
      y.val = z F ζ hζ V ε (projection j x).val := by
    intro y
    have hy : q F ζ hζ V y.val ∈
        (q F ζ hζ V) '' (L.compact : Set (CoveredSpherical F ζ hζ V)) :=
      ⟨y.val, y.property, rfl⟩
    obtain ⟨n, hn, hbase⟩ := Set.mem_iUnion₂.mp (hs hy)
    obtain ⟨w, hw⟩ := hbase
    have hq : q F ζ hζ V (Quotient.mk (coveredRelation F ζ hζ V)
        (w.val, (H.atlas V).representative (cov.chart n).component)) = q F ζ hζ V y.val := by
      rw [q_representative]
      exact hw
    obtain ⟨ε, hε⟩ := (KPContSectorQuotientRelationsComparison.q_eq_iff F ζ hζ V
      (Quotient.mk (coveredRelation F ζ hζ V)
        (w.val, (H.atlas V).representative (cov.chart n).component)) y.val).mp hq
    let j : Fin s.card := e.symm ⟨n, hn⟩
    have hj : nOf j = n := by
      change (e (e.symm ⟨n, hn⟩)).val = n
      rw [Equiv.apply_symm_apply]
    have hj' : component j = (cov.chart n).component := by
      change (cov.chart (nOf j)).component = (cov.chart n).component
      rw [hj]
    have hcp : chartPoint F ζ hζ C R P H U (chart j)
        (coordsInv F (KPContCotangentActualOverlap.labeledAInv places w.val)) =
        Quotient.mk (coveredRelation F ζ hζ V)
          (w.val, (H.atlas V).representative (cov.chart n).component) := by
      unfold chartPoint
      rw [KPContCotangentActualOverlap.ChartKind.representative]
      simp only [one_smul]
      rw [coordinates_coordsInv, labeledA_labeledAInv_of, hj']
    have hmem : Quotient.mk (coveredRelation F ζ hζ V)
        (w.val, (H.atlas V).representative (cov.chart n).component) ∈
        (L.compact : Set (CoveredSpherical F ζ hζ V)) :=
      (L.central_invariant ε _).mpr (by rw [← hε]; exact y.property)
    let x : piece j :=
      ⟨coordsInv F (KPContCotangentActualOverlap.labeledAInv places w.val), by
        refine ⟨?_, ?_⟩
        · refine ⟨KPContCotangentActualOverlap.labeledAInv places w.val, ?_, rfl⟩
          refine ⟨w.val, ?_, rfl⟩
          rw [hj]
          exact subset_closure w.property
        · show chartPoint F ζ hζ C R P H U (chart j)
            (coordsInv F (KPContCotangentActualOverlap.labeledAInv places w.val)) ∈
            (L.compact : Set (CoveredSpherical F ζ hζ V))
          rw [hcp]
          exact hmem⟩
    refine ⟨j, x, ε, ?_⟩
    have hxval : (projection j x).val = chartPoint F ζ hζ C R P H U (chart j)
        (coordsInv F (KPContCotangentActualOverlap.labeledAInv places w.val)) := rfl
    rw [hxval, hcp]
    exact hε
  let coverData : FiniteChartCover F ζ hζ C R P H U L :=
    { count := s.card,
      component := component,
      chart := chart,
      outer := outer,
      outer_contained := outer_contained,
      piece := piece,
      piece_eq := fun j => rfl,
      projection := projection,
      projection_formula := fun j x => rfl,
      phase := phase,
      phase_formula := fun j x => rfl,
      covers := covers }
  exact ⟨coverData⟩

variable (A : FiniteChartCover F ζ hζ C R P H U L)

abbrev PieceSpace := ∀ j : Fin A.count, C(A.piece j, ℂ)

def frameRestriction (v : KPContActualCompactSectorL2Map.E_L F ζ hζ V R L) :
    PieceSpace F ζ hζ C R P H U L A :=
  fun j => A.phase j * v.val.comp (A.projection j)

@[simp] theorem frameRestriction_apply
    (v : KPContActualCompactSectorL2Map.E_L F ζ hζ V R L) (j) (x : A.piece j) :
    frameRestriction F ζ hζ C R P H U L A v j x =
      A.phase j x * v.val (A.projection j x) := rfl

theorem phase_norm (j) (x : A.piece j) : ‖A.phase j x‖ = 1 := by
  rw [A.phase_formula]
  exact chi_norm F ζ hζ _

def frameRestrictionLinear : KPContActualCompactSectorL2Map.E_L F ζ hζ V R L →ₗ[ℂ]
    PieceSpace F ζ hζ C R P H U L A where
  toFun := frameRestriction F ζ hζ C R P H U L A
  map_add' v w := by
    funext j
    ext x
    simp only [frameRestriction_apply, Submodule.coe_add, ContinuousMap.add_apply,
      Pi.add_apply, mul_add]
  map_smul' c v := by
    funext j
    ext x
    simp only [frameRestriction_apply, Submodule.coe_smul, ContinuousMap.smul_apply,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem frameRestriction_norm
    (v : KPContActualCompactSectorL2Map.E_L F ζ hζ V R L) :
    ‖frameRestriction F ζ hζ C R P H U L A v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro j
    apply (ContinuousMap.norm_le _ (norm_nonneg v)).mpr
    intro x
    rw [frameRestriction_apply, norm_mul, phase_norm, one_mul]
    exact v.val.norm_coe_le_norm _
  · change ‖v.val‖ ≤ _
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro y
    obtain ⟨j, x, ε, hy⟩ := A.covers y
    have he : v.val y = (chi F ζ hζ ε : ℂ) * v.val (A.projection j x) := by
      have hv := v.property ε (A.projection j x)
      have hy' : y = ⟨z F ζ hζ V ε (A.projection j x).val,
          (L.central_invariant ε (A.projection j x).val).mp (A.projection j x).property⟩ :=
        Subtype.ext hy
      rw [hy']
      exact hv
    rw [he, norm_mul, Circle.norm_coe, one_mul]
    have hp := (frameRestriction F ζ hζ C R P H U L A v j).norm_coe_le_norm x
    rw [frameRestriction_apply, norm_mul, phase_norm, one_mul] at hp
    exact hp.trans (norm_le_pi_norm _ j)

def frameRestrictionIsometry : KPContActualCompactSectorL2Map.E_L F ζ hζ V R L →ₗᵢ[ℂ]
    PieceSpace F ζ hζ C R P H U L A where
  toLinearMap := frameRestrictionLinear F ζ hζ C R P H U L A
  norm_map' := frameRestriction_norm F ζ hζ C R P H U L A

theorem frameRestriction_smooth
    (w : KPContActualCutoffSmoothDescent.SmoothSections F ζ hζ C R P H U)
    (v : KPContActualCompactSectorL2Map.E_L F ζ hζ V R L)
    (hv : ∀ y : L.compact, v.val y =
      KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U w y.val)
    (j) (x : A.piece j) :
    frameRestrictionIsometry F ζ hζ C R P H U L A v j x =
      KPContActualCutoffChartJetHolomorphy.framePullback F ζ hζ C R P H U (A.chart j) w x.val := by
  change A.phase j x * v.val (A.projection j x) = _
  rw [hv, A.phase_formula, A.projection_formula]
  have hs : KPContSectorScalarLineAlgebra.S F ζ hζ V R P H
      ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ V R P H).symm w).val = w.val :=
    congrArg Subtype.val ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ V R P H).apply_symm_apply w)
  unfold KPContActualCutoffChartJetHolomorphy.framePullback KPContCotangentActualOverlap.LiftedChart.coefficient
  rw [← hs]
  rw [S_apply]
  rfl

theorem genuine_isClosed : IsClosed
    (KPContActualCompactSectorL2Map.E_L F ζ hζ V R L : Set (ContinuousMap L.compact ℂ)) := by
  have he : (KPContActualCompactSectorL2Map.E_L F ζ hζ V R L : Set (ContinuousMap L.compact ℂ)) =
      ⋂ (ε : rootsOfUnity 3 F) (x : L.compact),
        {v | v ⟨z F ζ hζ V ε x.val, (L.central_invariant ε x.val).mp x.property⟩ =
          (chi F ζ hζ ε : ℂ) * v x} := by
    ext v
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [he]
  apply isClosed_iInter
  intro ε
  apply isClosed_iInter
  intro x
  exact isClosed_eq ((ContinuousMap.evalCLM ℂ _).continuous)
    (continuous_const.mul ((ContinuousMap.evalCLM ℂ _).continuous))

theorem frameRestriction_closedRange : IsClosed (Set.range
    (frameRestrictionIsometry F ζ hζ C R P H U L A)) := by
  letI : CompleteSpace (KPContActualCompactSectorL2Map.E_L F ζ hζ V R L) :=
    (genuine_isClosed F ζ hζ C R P H U L).completeSpace_coe
  exact (frameRestrictionIsometry F ζ hζ C R P H U L A).isometry.isClosedEmbedding.isClosed_range

theorem isometry_differentiableOn {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (T : E →ₗᵢ[ℂ] Y) (hc : IsClosed (Set.range T))
    (g : ℂ → E) (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ (fun s => T (g s)) Ω) : DifferentiableOn ℂ g Ω := by
  intro s hs
  have hd := (hg s hs).differentiableAt (hΩ.mem_nhds hs)
  have ht := hd.hasDerivAt.tendsto_slope
  have hr : deriv (fun s => T (g s)) s ∈ Set.range T := by
    apply hc.mem_of_tendsto ht
    exact Filter.Eventually.of_forall fun t =>
      ⟨slope g s t, by simp [slope_def_module, map_smul, map_sub]⟩
  obtain ⟨d, hd'⟩ := hr
  have hlim : Filter.Tendsto (fun t => T (slope g s t)) (𝓝[≠] s) (𝓝 (T d)) := by
    convert ht using 1
    · funext t
      simp only [slope_def_module, map_smul, map_sub]
    · rw [hd']
  have hl := T.isometry.isEmbedding.isInducing.tendsto_nhds_iff.mpr hlim
  exact (hasDerivAt_iff_tendsto_slope.mpr hl).differentiableAt.differentiableWithinAt

end DedekindZetaZeroFree.CompactChartRestriction

end
