module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Spherical.LocalSmoothSolutionFamilies

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSmoothLineGluing

open KPContLocalNorm KPContActualChartRestrictionDensity
open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts
open KPContSectorScalarLineAlgebra KPContSectorSmoothFramesSupport
open KPContSectorLineL2Isometry KPContSectorFixedPushforwardSupport

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

structure LocalSection (V : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) where
  scalar : GenuineCoveredScalars F ζ hζ U
  outside : ∀ v, q F ζ hζ U v ∉ V → scalar.val v = 0

structure Separation : Prop where
  local_sections : ∀ (V : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)), IsOpen V →
    ∀ w w' : LocalSection F ζ hζ U V,
      ContinuousOn w.scalar.val (q F ζ hζ U ⁻¹' V) →
      ContinuousOn w'.scalar.val (q F ζ hζ U ⁻¹' V) →
      (w.scalar.val =ᵐ[(coveredMeasure F ζ hζ R U).restrict (q F ζ hζ U ⁻¹' V)]
        w'.scalar.val) →
      Set.EqOn w.scalar.val w'.scalar.val (q F ζ hζ U ⁻¹' V)

  frame_overlaps : ∀ (i : Fin (H.atlas U).componentCount)
    (γ : Component F ζ hζ U R P H i) (ε : rootsOfUnity 3 F)
    (D : Set (Space (KPCuspLogShape.dimension F * 3))), IsOpen D →
    ∀ f g : Space (KPCuspLogShape.dimension F * 3) → ℂ,
      ContinuousOn f D →
      ContinuousOn (fun p => (overlapTransition F ζ hζ U R P H i γ ε : ℂ) *
        g (overlapCoordinate F ζ hζ U R P H i γ p)) D →
      (f =ᵐ[volume.restrict D]
        (fun p => (overlapTransition F ζ hζ U R P H i γ ε : ℂ) *
          g (overlapCoordinate F ζ hζ U R P H i γ p))) →
      Set.EqOn f (fun p => (overlapTransition F ζ hζ U R P H i γ ε : ℂ) *
        g (overlapCoordinate F ζ hζ U R P H i γ p)) D

structure ChartBall where
  component : Fin (H.atlas U).componentCount
  center : SymmetricSpace F
  chart : OrbifoldChart F ζ hζ U R P H component center
  phase : PhaseSheets F ζ hζ U
  ball : LocalBall (KPCuspLogShape.dimension F * 3)
  contained : KPContLocalCubeEmbedding.closedCarrier ball ⊆
    chartDomain F ζ hζ U R P H component center chart

def coefficient (w : Sections F ζ hζ U R P H) (A : ChartBall F ζ hζ U R P H) :
    Space (KPCuspLogShape.dimension F * 3) → ℂ :=
  frameCoefficient F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H w)
    A.component A.phase

def Represents (w : Sections F ζ hζ U R P H)
    (v : KPContSectorClosedLpSubspace.H F ζ hζ R U) : Prop :=
  ∃ hf : MemLp (scalarRepresentative F ζ hζ U R P H w).val 2
      (coveredMeasure F ζ hζ R U),
    hf.toLp (scalarRepresentative F ζ hζ U R P H w).val =
      (v : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U)

theorem section_ext (w w' : Sections F ζ hζ U R P H)
    (h : ∀ A : ChartBall F ζ hζ U R P H,
      Set.EqOn (coefficient F ζ hζ U R P H w A)
        (coefficient F ζ hζ U R P H w' A) A.ball.carrier) :
    w = w' := by
  funext i
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨O⟩ := orbifoldChart_exists F ζ hζ U R P H i x
  let p : Space (KPCuspLogShape.dimension F * 3) := (coordinates F).symm x
  have hpx : coordinates F p = x := (coordinates F).apply_symm_apply x
  have hmem : p ∈ chartDomain F ζ hζ U R P H i x O := by
    show coordinates F p ∈ O.neighborhood
    rw [hpx]; exact O.center_mem
  have hOpen : IsOpen (chartDomain F ζ hζ U R P H i x O) :=
    O.isOpen.preimage (coordinates F).continuous
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hOpen.mem_nhds hmem)
  let B : LocalBall (KPCuspLogShape.dimension F * 3) :=
    ⟨Nat.mul_pos (KPCuspLogShape.dimension_pos F H.totallyComplex) (by norm_num),
      p, r, hr⟩
  have hBc : KPContLocalCubeEmbedding.closedCarrier B ⊆
      chartDomain F ζ hζ U R P H i x O := hrU
  have hpB : p ∈ B.carrier := by
    rw [KPContLocalNorm.LocalBall.carrier]; exact Metric.mem_ball_self hr
  let A : ChartBall F ζ hζ U R P H := ⟨i, x, O, phaseClass F ζ hζ U 1, B, hBc⟩
  have hval : ∀ v : Sections F ζ hζ U R P H,
      coefficient F ζ hζ U R P H v A p = (v i).val x := by
    intro v
    show frameCoefficient F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H v) i
      (phaseClass F ζ hζ U 1) p = _
    rw [frameCoefficient_class, map_one,
      scalarRepresentative_eq_symm, LinearEquiv.apply_symm_apply, hpx]
    simp
  have := h A hpB
  rw [hval w, hval w'] at this
  exact this

theorem overlapCoordinate_continuous (i : Fin (H.atlas U).componentCount)
    (γ : Component F ζ hζ U R P H i) :
    Continuous (overlapCoordinate F ζ hζ U R P H i γ) :=
  (coordinates F).symm.continuous.comp
    ((KPCuspSiegel.continuous_action F γ.val).comp (coordinates F).continuous)

theorem exists_canonicalData (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F) :
    ∃ (O : OrbifoldChart F ζ hζ U R P H i x)
      (B : LocalBall (KPCuspLogShape.dimension F * 3)),
      KPContLocalCubeEmbedding.closedCarrier B ⊆ chartDomain F ζ hζ U R P H i x O ∧
      (coordinates F).symm x ∈ B.carrier := by
  obtain ⟨O⟩ := orbifoldChart_exists F ζ hζ U R P H i x
  let p : Space (KPCuspLogShape.dimension F * 3) := (coordinates F).symm x
  have hpx : coordinates F p = x := (coordinates F).apply_symm_apply x
  have hmem : p ∈ chartDomain F ζ hζ U R P H i x O := by
    show coordinates F p ∈ O.neighborhood
    rw [hpx]; exact O.center_mem
  have hOpen : IsOpen (chartDomain F ζ hζ U R P H i x O) :=
    O.isOpen.preimage (coordinates F).continuous
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hOpen.mem_nhds hmem)
  refine ⟨O, ⟨Nat.mul_pos (KPCuspLogShape.dimension_pos F H.totallyComplex) (by norm_num),
    p, r, hr⟩, hrU, ?_⟩
  rw [KPContLocalNorm.LocalBall.carrier]
  exact Metric.mem_ball_self hr

def canonicalChart (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F) :
    OrbifoldChart F ζ hζ U R P H i x :=
  Classical.choose (exists_canonicalData F ζ hζ U R P H i x)

def canonicalBall (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F) :
    LocalBall (KPCuspLogShape.dimension F * 3) :=
  Classical.choose (Classical.choose_spec (exists_canonicalData F ζ hζ U R P H i x))

theorem canonicalBall_contained (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F) :
    KPContLocalCubeEmbedding.closedCarrier (canonicalBall F ζ hζ U R P H i x) ⊆
      chartDomain F ζ hζ U R P H i x (canonicalChart F ζ hζ U R P H i x) :=
  (Classical.choose_spec (Classical.choose_spec (exists_canonicalData F ζ hζ U R P H i x))).1

theorem canonicalBall_mem (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F) :
    (coordinates F).symm x ∈ (canonicalBall F ζ hζ U R P H i x).carrier :=
  (Classical.choose_spec (Classical.choose_spec (exists_canonicalData F ζ hζ U R P H i x))).2

def canonicalChartBall (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (m : PhaseSheets F ζ hζ U) : ChartBall F ζ hζ U R P H :=
  ⟨i, x, canonicalChart F ζ hζ U R P H i x, m, canonicalBall F ζ hζ U R P H i x,
    canonicalBall_contained F ζ hζ U R P H i x⟩

theorem canonicalChartBall_mem (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F) (m : PhaseSheets F ζ hζ U) :
    (coordinates F).symm x ∈ (canonicalChartBall F ζ hζ U R P H i x m).ball.carrier :=
  canonicalBall_mem F ζ hζ U R P H i x

theorem exists_canonicalChartBall (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F) (m : PhaseSheets F ζ hζ U) :
    ∃ A : ChartBall F ζ hζ U R P H,
      A.component = i ∧ A.center = x ∧ A.phase = m ∧
        (coordinates F).symm x ∈ A.ball.carrier :=
  ⟨canonicalChartBall F ζ hζ U R P H i x m, rfl, rfl, rfl,
    canonicalChartBall_mem F ζ hζ U R P H i x m⟩

structure LocalRepresentatives (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U) where
  coefficient : ChartBall F ζ hζ U R P H → ℂ → Space (KPCuspLogShape.dimension F * 3) → ℂ
  smooth : ∀ A s, s ∈ Ω → ContDiffOn ℝ (⊤ : ℕ∞) (coefficient A s) A.ball.carrier
  represents : ∀ A s, s ∈ Ω →
    coefficient A s =ᵐ[volume.restrict A.ball.carrier]
      (fun p => restriction F ζ hζ U R P H A.component A.center A.chart A.phase
        A.ball A.contained (u s) p)

theorem local_overlap (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (i : Fin (H.atlas U).componentCount) (x y : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (O' : OrbifoldChart F ζ hζ U R P H i y)
    (m m' : PhaseSheets F ζ hζ U) (ε : rootsOfUnity 3 F)
    (γ : Component F ζ hζ U R P H i)
    (B B' : LocalBall (KPCuspLogShape.dimension F * 3))
    (hB : KPContLocalCubeEmbedding.closedCarrier B ⊆ chartDomain F ζ hζ U R P H i x O)
    (hB' : KPContLocalCubeEmbedding.closedCarrier B' ⊆ chartDomain F ζ hζ U R P H i y O')
    (hm : m = phaseClass F ζ hζ U ε * m') (s : ℂ) (hs : s ∈ Ω) :
    ∀ p ∈ B.carrier ∩ overlapCoordinate F ζ hζ U R P H i γ ⁻¹' B'.carrier,
      locals.coefficient ⟨i, x, O, m, B, hB⟩ s p =
        (overlapTransition F ζ hζ U R P H i γ ε : ℂ) *
          locals.coefficient ⟨i, y, O', m', B', hB'⟩ s
            (overlapCoordinate F ζ hζ U R P H i γ p) := by
  intro p hp
  have hcont : Continuous (overlapCoordinate F ζ hζ U R P H i γ) :=
    overlapCoordinate_continuous F ζ hζ U R P H i γ
  have hU : IsOpen (B.carrier ∩ overlapCoordinate F ζ hζ U R P H i γ ⁻¹' B'.carrier) :=
    Metric.isOpen_ball.inter (hcont.isOpen_preimage _ Metric.isOpen_ball)
  have ha : locals.coefficient ⟨i, x, O, m, B, hB⟩ s =ᵐ[volume.restrict B.carrier]
      restriction F ζ hζ U R P H i x O m B hB (u s) :=
    locals.represents ⟨i, x, O, m, B, hB⟩ s hs
  have hb : locals.coefficient ⟨i, y, O', m', B', hB'⟩ s =ᵐ[volume.restrict B'.carrier]
      restriction F ζ hζ U R P H i y O' m' B' hB' (u s) :=
    locals.represents ⟨i, y, O', m', B', hB'⟩ s hs
  have hb' : ∀ᵐ q ∂volume, q ∈ B'.carrier →
      locals.coefficient ⟨i, y, O', m', B', hB'⟩ s q =
        restriction F ζ hζ U R P H i y O' m' B' hB' (u s) q :=
    (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hb
  have hτ := (overlapCoordinate_quasiMeasurePreserving F ζ hζ U R P H i γ).ae hb'
  have hrel := restriction_overlap F ζ hζ U R P H i x y O O' m m' ε γ B B' hB hB' hm (u s)
  have haS : locals.coefficient ⟨i, x, O, m, B, hB⟩ s =ᵐ[
      volume.restrict (B.carrier ∩ overlapCoordinate F ζ hζ U R P H i γ ⁻¹' B'.carrier)]
      restriction F ζ hζ U R P H i x O m B hB (u s) :=
    ha.filter_mono (Measure.absolutelyContinuous_of_le
      (Measure.restrict_mono (s := B.carrier ∩ overlapCoordinate F ζ hζ U R P H i γ ⁻¹' B'.carrier)
        Set.inter_subset_left le_rfl)).ae_le
  have hrelS : restriction F ζ hζ U R P H i x O m B hB (u s) =ᵐ[
      volume.restrict (B.carrier ∩ overlapCoordinate F ζ hζ U R P H i γ ⁻¹' B'.carrier)]
      (fun q => (overlapTransition F ζ hζ U R P H i γ ε : ℂ) *
        restriction F ζ hζ U R P H i y O' m' B' hB' (u s)
          (overlapCoordinate F ζ hζ U R P H i γ q)) :=
    hrel
  have hτS : ∀ᵐ q ∂volume.restrict
      (B.carrier ∩ overlapCoordinate F ζ hζ U R P H i γ ⁻¹' B'.carrier),
      overlapCoordinate F ζ hζ U R P H i γ q ∈ B'.carrier →
        locals.coefficient ⟨i, y, O', m', B', hB'⟩ s
            (overlapCoordinate F ζ hζ U R P H i γ q) =
          restriction F ζ hζ U R P H i y O' m' B' hB' (u s)
            (overlapCoordinate F ζ hζ U R P H i γ q) :=
    hτ.filter_mono (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le
  have hae : locals.coefficient ⟨i, x, O, m, B, hB⟩ s =ᵐ[
      volume.restrict (B.carrier ∩ overlapCoordinate F ζ hζ U R P H i γ ⁻¹' B'.carrier)]
      (fun q => (overlapTransition F ζ hζ U R P H i γ ε : ℂ) *
        locals.coefficient ⟨i, y, O', m', B', hB'⟩ s
          (overlapCoordinate F ζ hζ U R P H i γ q)) := by
    filter_upwards [haS, hrelS, hτS, ae_restrict_mem hU.measurableSet] with q h1 h2 h3 hmem
    rw [h1, h2, h3 hmem.2]
  have hcont1 : ContinuousOn (locals.coefficient ⟨i, x, O, m, B, hB⟩ s)
      (B.carrier ∩ overlapCoordinate F ζ hζ U R P H i γ ⁻¹' B'.carrier) :=
    (locals.smooth ⟨i, x, O, m, B, hB⟩ s hs).continuousOn.mono Set.inter_subset_left
  have hcont2 : ContinuousOn (fun q => (overlapTransition F ζ hζ U R P H i γ ε : ℂ) *
      locals.coefficient ⟨i, y, O', m', B', hB'⟩ s
        (overlapCoordinate F ζ hζ U R P H i γ q))
      (B.carrier ∩ overlapCoordinate F ζ hζ U R P H i γ ⁻¹' B'.carrier) :=
    continuousOn_const.mul
      (((locals.smooth ⟨i, y, O', m', B', hB'⟩ s hs).continuousOn).comp
        hcont.continuousOn (fun q hq => hq.2))
  exact Measure.eqOn_open_of_ae_eq hae hU hcont1 hcont2 hp

theorem overlapCoordinate_one (i : Fin (H.atlas U).componentCount)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    overlapCoordinate F ζ hζ U R P H i 1 p = p := by
  simp [overlapCoordinate]

theorem overlapTransition_one (i : Fin (H.atlas U).componentCount)
    (ε : rootsOfUnity 3 F) :
    (overlapTransition F ζ hζ U R P H i 1 ε : ℂ) = (chi F ζ hζ ε : ℂ) := by
  simp [overlapTransition, map_one]

structure Gluing (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u) where
  representative : ℂ → smoothSections F ζ hζ U R P H
  coefficients : ∀ s ∈ Ω, ∀ A,
    Set.EqOn (coefficient F ζ hζ U R P H (representative s).val A)
      (locals.coefficient A s) A.ball.carrier
  represents : ∀ s ∈ Ω, Represents F ζ hζ U R P H (representative s).val (u s)
  unique : ∀ s ∈ Ω, ∀ w : smoothSections F ζ hζ U R P H,
    (∀ A, Set.EqOn (coefficient F ζ hζ U R P H w.val A)
      (locals.coefficient A s) A.ball.carrier) → w = representative s

  group_lift : ∀ s ∈ Ω, ∀ (a : KPSmoothActualFlowData.GInfinity F)
    (c : FiniteCover F ζ hζ),
    (scalarRepresentative F ζ hζ U R P H (representative s).val).val
      (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
          (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
            (c : ActualCover F ζ hζ)))) =
      (J F ζ hζ U (scalarRepresentative F ζ hζ U R P H (representative s).val)).val
        (KPMsFixedHaarDisintegration.archBasepoint F a, c)

def HasLocalPromotions (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u) : Prop :=
  ∀ A : ChartBall F ζ hζ U R P H,
    ∃ promotion : KPContActualLocalSolutionFamily.Promotion F ζ hζ U R P H
      A.component A.center A.chart A.phase A.ball A.contained Ω u,
      ∀ s ∈ Ω, Set.EqOn (promotion.representative s) (locals.coefficient A s) A.ball.carrier

structure HolomorphicData (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (W : ℂ → smoothSections F ζ hζ U R P H) : Prop where
  holomorphic : ∀ A : ChartBall F ζ hζ U R P H,
    KPCutoffSource.ChartSmoothHolomorphicOn A.ball
      (fun s => coefficient F ζ hζ U R P H (W s).val A) Ω
  disks : ∀ (c : ℂ) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ Ω →
    ∃ b : ℕ → smoothSections F ζ hζ U R P H,
      (∀ j, Represents F ζ hζ U R P H (b j).val
        ((cauchyPowerSeries u c r j) (fun _ => 1))) ∧
      (∀ j (w : smoothSections F ζ hζ U R P H),
        Represents F ζ hζ U R P H w.val ((cauchyPowerSeries u c r j) (fun _ => 1)) →
        w = b j) ∧
      (∀ A : ChartBall F ζ hζ U R P H,
        SmoothPowerSeriesOn A.ball c r
          (fun j => coefficient F ζ hζ U R P H (b j).val A)
          (fun s => coefficient F ζ hζ U R P H (W s).val A)) ∧

      (∀ (A : ChartBall F ζ hζ U R P H) j
        (f : Space (KPCuspLogShape.dimension F * 3) → ℂ),
        ContDiffOn ℝ (⊤ : ℕ∞) f A.ball.carrier →
        (f =ᵐ[volume.restrict A.ball.carrier]
          (fun p => restriction F ζ hζ U R P H A.component A.center A.chart A.phase
            A.ball A.contained ((cauchyPowerSeries u c r j) (fun _ => 1)) p)) →
        Set.EqOn f (coefficient F ζ hζ U R P H (b j).val A) A.ball.carrier)

structure Contract : Prop where
  separation : Separation F ζ hζ U R P H
  gluing : ∀ (Ω : Set ℂ), IsOpen Ω →
    ∀ (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
      (locals : LocalRepresentatives F ζ hζ U R P H Ω u),
      Nonempty (Gluing F ζ hζ U R P H Ω u locals)
  promotion : ∀ (Ω : Set ℂ), IsOpen Ω →
    ∀ (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
      (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
      (glued : Gluing F ζ hζ U R P H Ω u locals),
      HasLocalPromotions F ζ hζ U R P H Ω u locals →
      HolomorphicData F ζ hζ U R P H Ω u glued.representative

theorem separation_of_realization
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    Separation F ζ hζ U R P H := by
  haveI : (coveredMeasure F ζ hζ R U).IsOpenPosMeasure :=
    realization.support.covered_open_positive
  refine ⟨?_, ?_⟩
  · intro V hV w w' hw hw' hae
    exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae
      (hV.preimage (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U)) hw hw'
  · intro i γ ε D hD f g hf hg hae
    exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae hD hf hg

def patchedCoefficient (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (i : Fin (H.atlas U).componentCount) (m : PhaseSheets F ζ hζ U)
    (s : ℂ) (p : Space (KPCuspLogShape.dimension F * 3)) : ℂ :=
  locals.coefficient (canonicalChartBall F ζ hζ U R P H i (coordinates F p) m) s p

theorem patchedCoefficient_eq_local (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (s : ℂ) (hs : s ∈ Ω) (A : ChartBall F ζ hζ U R P H)
    (p : Space (KPCuspLogShape.dimension F * 3)) (hp : p ∈ A.ball.carrier) :
    patchedCoefficient F ζ hζ U R P H Ω u locals A.component A.phase s p =
      locals.coefficient A s p := by
  have hcan : p ∈ (canonicalBall F ζ hζ U R P H A.component (coordinates F p)).carrier := by
    simpa only [Homeomorph.symm_apply_apply] using
      canonicalBall_mem F ζ hζ U R P H A.component (coordinates F p)
  have h := local_overlap F ζ hζ U R P H Ω u locals A.component (coordinates F p) A.center
    (canonicalChart F ζ hζ U R P H A.component (coordinates F p)) A.chart
    A.phase A.phase 1 1
    (canonicalBall F ζ hζ U R P H A.component (coordinates F p)) A.ball
    (canonicalBall_contained F ζ hζ U R P H A.component (coordinates F p)) A.contained
    (by simp) s hs p ⟨hcan, by simpa only [Set.mem_preimage, overlapCoordinate_one] using hp⟩
  simpa only [patchedCoefficient, canonicalChartBall, overlapCoordinate_one,
    overlapTransition_one, map_one, Circle.coe_one, one_mul] using h

theorem patchedCoefficient_smooth (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (i : Fin (H.atlas U).componentCount) (m : PhaseSheets F ζ hζ U)
    (s : ℂ) (hs : s ∈ Ω) :
    ContDiff ℝ (⊤ : ℕ∞) (patchedCoefficient F ζ hζ U R P H Ω u locals i m s) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  let A := canonicalChartBall F ζ hζ U R P H i (coordinates F p) m
  have hp : p ∈ A.ball.carrier := by
    simpa only [Homeomorph.symm_apply_apply] using
      canonicalChartBall_mem F ζ hζ U R P H i (coordinates F p) m
  have he : patchedCoefficient F ζ hζ U R P H Ω u locals i m s =ᶠ[𝓝 p]
      locals.coefficient A s :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hp) fun q hq =>
      patchedCoefficient_eq_local F ζ hζ U R P H Ω u locals s hs A q hq
  exact ((locals.smooth A s hs p hp).contDiffAt (Metric.isOpen_ball.mem_nhds hp)).congr_of_eventuallyEq he

theorem patchedCoefficient_overlap (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (i : Fin (H.atlas U).componentCount) (m m' : PhaseSheets F ζ hζ U)
    (ε : rootsOfUnity 3 F) (γ : Component F ζ hζ U R P H i)
    (hm : m = phaseClass F ζ hζ U ε * m') (s : ℂ) (hs : s ∈ Ω)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    patchedCoefficient F ζ hζ U R P H Ω u locals i m s p =
      (overlapTransition F ζ hζ U R P H i γ ε : ℂ) *
        patchedCoefficient F ζ hζ U R P H Ω u locals i m' s
          (overlapCoordinate F ζ hζ U R P H i γ p) := by
  let q := overlapCoordinate F ζ hζ U R P H i γ p
  have hp : p ∈ (canonicalBall F ζ hζ U R P H i (coordinates F p)).carrier := by
    simpa only [Homeomorph.symm_apply_apply] using canonicalBall_mem F ζ hζ U R P H i (coordinates F p)
  have hq : q ∈ (canonicalBall F ζ hζ U R P H i (coordinates F q)).carrier := by
    simpa only [Homeomorph.symm_apply_apply] using canonicalBall_mem F ζ hζ U R P H i (coordinates F q)
  exact local_overlap F ζ hζ U R P H Ω u locals i (coordinates F p) (coordinates F q)
    (canonicalChart F ζ hζ U R P H i (coordinates F p))
    (canonicalChart F ζ hζ U R P H i (coordinates F q)) m m' ε γ
    (canonicalBall F ζ hζ U R P H i (coordinates F p))
    (canonicalBall F ζ hζ U R P H i (coordinates F q))
    (canonicalBall_contained F ζ hζ U R P H i (coordinates F p))
    (canonicalBall_contained F ζ hζ U R P H i (coordinates F q)) hm s hs p ⟨hp, hq⟩

theorem patchedCoefficient_mem_fiber (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (i : Fin (H.atlas U).componentCount) (s : ℂ) (hs : s ∈ Ω)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    patchedCoefficient F ζ hζ U R P H Ω u locals i (phaseClass F ζ hζ U 1) s p ∈
      KPCuspGenuineMonodromy.scalarFiber F ζ hζ U := by
  intro ε hε
  have hphase : phaseClass F ζ hζ U ε = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hε
  have he := patchedCoefficient_overlap F ζ hζ U R P H Ω u locals i
    (phaseClass F ζ hζ U 1) (phaseClass F ζ hζ U 1) ε 1
    (by rw [hphase, one_mul]) s hs p
  simpa only [overlapCoordinate_one, overlapTransition_one, chi_coe] using he.symm

def patchedSections (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (s : ℂ) (hs : s ∈ Ω) : Sections F ζ hζ U R P H := by
  intro i
  refine ⟨fun x => patchedCoefficient F ζ hζ U R P H Ω u locals i
    (phaseClass F ζ hζ U 1) s ((coordinates F).symm x), ?_, ?_⟩
  · intro x
    exact patchedCoefficient_mem_fiber F ζ hζ U R P H Ω u locals i s hs _
  · intro γ x
    let a : ℂ := (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line i).rho γ) : ℂ)
    have ha : a ≠ 0 := Units.ne_zero _
    have he := patchedCoefficient_overlap F ζ hζ U R P H Ω u locals i
      (phaseClass F ζ hζ U 1) (phaseClass F ζ hζ U 1) 1 γ (by simp) s hs
      ((coordinates F).symm x)
    have he' : patchedCoefficient F ζ hζ U R P H Ω u locals i
        (phaseClass F ζ hζ U 1) s ((coordinates F).symm x) = a⁻¹ *
      patchedCoefficient F ζ hζ U R P H Ω u locals i (phaseClass F ζ hζ U 1) s
        ((coordinates F).symm ((γ : KPCuspArithmetic.PGL2 F) • x)) := by
      simpa only [overlapCoordinate, Homeomorph.apply_symm_apply, overlapTransition,
        map_one, Circle.coe_mul, Circle.coe_one, one_mul, map_inv, Circle.coe_inv] using
        (show _ from he.trans (congrArg (fun z : ℂ => z *
          patchedCoefficient F ζ hζ U R P H Ω u locals i (phaseClass F ζ hζ U 1) s
            (overlapCoordinate F ζ hζ U R P H i γ ((coordinates F).symm x)))
          (by simp only [overlapTransition, map_one, Circle.coe_mul, Circle.coe_one, one_mul,
            map_inv, Circle.coe_inv]; rw [chi_coe])))
    calc
      _ = a * (a⁻¹ * patchedCoefficient F ζ hζ U R P H Ω u locals i
          (phaseClass F ζ hζ U 1) s ((coordinates F).symm ((γ : KPCuspArithmetic.PGL2 F) • x))) := by
        rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
      _ = a * patchedCoefficient F ζ hζ U R P H Ω u locals i
          (phaseClass F ζ hζ U 1) s ((coordinates F).symm x) := congrArg (fun z : ℂ => a * z) he'.symm

def patchedSmoothSections (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (s : ℂ) (hs : s ∈ Ω) : smoothSections F ζ hζ U R P H := by
  refine ⟨patchedSections F ζ hζ U R P H Ω u locals s hs, ?_⟩
  intro i
  exact (patchedCoefficient_smooth F ζ hζ U R P H Ω u locals i (phaseClass F ζ hζ U 1) s hs).comp
    (CoreChartLocalizers.CutoffConstruction.ChartDensityConstruction.coordinates_symm_contDiff
      (KPCuspLogShape.dimension F))

theorem patchedSmoothSections_coefficients (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (s : ℂ) (hs : s ∈ Ω) (A : ChartBall F ζ hζ U R P H) :
    Set.EqOn (coefficient F ζ hζ U R P H
      (patchedSmoothSections F ζ hζ U R P H Ω u locals s hs).val A)
      (locals.coefficient A s) A.ball.carrier := by
  intro p hp
  obtain ⟨ε, hε⟩ := (QuotientGroup.mk'_surjective (centralLevel F ζ hζ U)) A.phase
  change phaseClass F ζ hζ U ε = A.phase at hε
  have he := patchedCoefficient_overlap F ζ hζ U R P H Ω u locals A.component
    A.phase (phaseClass F ζ hζ U 1) ε 1 (by simpa only [map_one, mul_one] using hε.symm) s hs p
  have he' : patchedCoefficient F ζ hζ U R P H Ω u locals A.component A.phase s p =
      (chi F ζ hζ ε : ℂ) * patchedCoefficient F ζ hζ U R P H Ω u locals A.component
        (phaseClass F ζ hζ U 1) s p := by
    simpa only [overlapCoordinate_one, overlapTransition_one] using he
  calc
    _ = (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      patchedCoefficient F ζ hζ U R P H Ω u locals A.component (phaseClass F ζ hζ U 1) s p := by
        change frameCoefficient F ζ hζ U R P H
          (scalarRepresentative F ζ hζ U R P H
            (patchedSmoothSections F ζ hζ U R P H Ω u locals s hs).val)
            A.component A.phase p = _
        rw [← hε, frameCoefficient_class, scalarRepresentative_eq_symm, LinearEquiv.apply_symm_apply]
        exact congrArg (fun z : ℂ => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * z)
          (congrArg (patchedCoefficient F ζ hζ U R P H Ω u locals A.component
            (phaseClass F ζ hζ U 1) s) ((coordinates F).symm_apply_apply p))
    _ = patchedCoefficient F ζ hζ U R P H Ω u locals A.component A.phase s p := by
      rw [← chi_coe]
      exact he'.symm
    _ = _ := patchedCoefficient_eq_local F ζ hζ U R P H Ω u locals s hs A p hp

theorem canonicalBalls_countable_cover (i : Fin (H.atlas U).componentCount) :
    ∃ T : Set (Space (KPCuspLogShape.dimension F * 3)), T.Countable ∧
      (Set.univ : Set (Space (KPCuspLogShape.dimension F * 3))) ⊆
        ⋃ p ∈ T, (canonicalBall F ζ hζ U R P H i (coordinates F p)).carrier := by
  apply isLindelof_univ.elim_countable_subcover
    (fun p => (canonicalBall F ζ hζ U R P H i (coordinates F p)).carrier)
    (fun _ => Metric.isOpen_ball)
  intro p _
  apply Set.mem_iUnion.mpr
  refine ⟨p, ?_⟩
  simpa only [Homeomorph.symm_apply_apply] using
    canonicalBall_mem F ζ hζ U R P H i (coordinates F p)

theorem patchedCoefficient_ae_representative (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (i : Fin (H.atlas U).componentCount) (m : PhaseSheets F ζ hζ U)
    (s : ℂ) (hs : s ∈ Ω) (f : BorelL2Scalars F ζ hζ U R)
    (hf : scalarEmbedding F ζ hζ U R P H f = u s) :
    patchedCoefficient F ζ hζ U R P H Ω u locals i m s =ᵐ[volume]
      frameCoefficient F ζ hζ U R P H f.val i m := by
  obtain ⟨T, hT, hcover⟩ := canonicalBalls_countable_cover F ζ hζ U R P H i
  let D := fun p : Space (KPCuspLogShape.dimension F * 3) =>
    (canonicalBall F ζ hζ U R P H i (coordinates F p)).carrier
  have hall : ∀ p ∈ T,
      patchedCoefficient F ζ hζ U R P H Ω u locals i m s =ᵐ[volume.restrict (D p)]
        frameCoefficient F ζ hζ U R P H f.val i m := by
    intro p _
    let A := canonicalChartBall F ζ hζ U R P H i (coordinates F p) m
    have hlocal := locals.represents A s hs
    have hexact := restriction_representative F ζ hζ U R P H A.component A.center A.chart
      A.phase A.ball A.contained (u s) f hf
    have hpoint : patchedCoefficient F ζ hζ U R P H Ω u locals i m s =ᵐ[volume.restrict A.ball.carrier]
        locals.coefficient A s := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with q hq
      exact patchedCoefficient_eq_local F ζ hζ U R P H Ω u locals s hs A q hq
    exact hpoint.trans (hlocal.trans hexact)
  have hae := (ae_restrict_biUnion_iff D hT
    (fun p => patchedCoefficient F ζ hζ U R P H Ω u locals i m s p =
      frameCoefficient F ζ hζ U R P H f.val i m p)).mpr hall
  have hfull : (⋃ p ∈ T, D p) = Set.univ := Set.eq_univ_of_univ_subset hcover
  rwa [hfull, Measure.restrict_univ] at hae

private theorem patchedComponent_ae (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (s : ℂ) (hs : s ∈ Ω) (f : BorelL2Scalars F ζ hζ U R)
    (hf : scalarEmbedding F ζ hζ U R P H f = u s)
    (i : Fin (H.atlas U).componentCount) :
    ((patchedSmoothSections F ζ hζ U R P H Ω u locals s hs).val i).val =ᵐ[
      KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)]
      (S F ζ hζ U R P H f.val i).val := by
  have ha := patchedCoefficient_ae_representative F ζ hζ U R P H Ω u locals i
    (phaseClass F ζ hζ U 1) s hs f hf
  have hb := (withDensity_absolutelyContinuous volume (fun p => ENNReal.ofReal (density F p))).ae_eq ha
  have hc : (fun p => ((patchedSmoothSections F ζ hζ U R P H Ω u locals s hs).val i).val
      (coordinates F p)) =ᵐ[volume.withDensity (fun p => ENNReal.ofReal (density F p))]
      (fun p => (S F ζ hζ U R P H f.val i).val (coordinates F p)) := by
    filter_upwards [hb] with p hp
    have hχ : (chi F ζ hζ (1 : rootsOfUnity 3 F) : ℂ) = 1 := by
      rw [chi_coe]
      exact congrArg (fun z : ℂˣ => (z : ℂ)) (map_one (KPCuspGenuineMonodromy.chi F ζ hζ))
    rw [frameCoefficient_class, hχ, one_mul] at hp
    simpa only [patchedSmoothSections, patchedSections, Homeomorph.symm_apply_apply] using hp
  have hmeas : ∀ i, Measurable (S F ζ hζ U R P H f.val i).val := by
    apply (borel_iff F ζ hζ U R P H (S F ζ hζ U R P H f.val)).mpr
    rw [scalarRepresentative_eq_symm, LinearEquiv.symm_apply_apply]
    exact f.property.1
  have he : ((patchedSmoothSections F ζ hζ U R P H Ω u locals s hs).val i).val =ᵐ[
      Measure.map (coordinates F) (volume.withDensity (fun p => ENNReal.ofReal (density F p)))]
      (S F ζ hζ U R P H f.val i).val :=
    (ae_map_iff ((coordinates F).continuous.measurable.aemeasurable)
      (measurableSet_eq_fun
        ((patchedSmoothSections F ζ hζ U R P H Ω u locals s hs).property i).continuous.measurable
        (hmeas i))).mpr hc
  rwa [metric_volume] at he

private theorem scalar_ae_of_component_ae (f g : GenuineCoveredScalars F ζ hζ U)
    (hf : Measurable f.val) (hg : Measurable g.val)
    (he : ∀ i, (S F ζ hζ U R P H f i).val =ᵐ[KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)]
      (S F ζ hζ U R P H g i).val) : f.val =ᵐ[coveredMeasure F ζ hζ R U] g.val := by
  let d := f - g
  have hd : Measurable d.val := hf.sub hg
  let N := kp_cont_sector_fixed_line_norm_integrals F ζ hζ U R P H d hd
  letI : ∀ i : Fin (H.atlas U).componentCount,
      OpensMeasurableSpace (KPCuspSiegel.OrbitQuotient F (Component F ζ hζ U R P H i)) :=
    fun i => ⟨MeasurableSpace.generateFrom_le (fun s hs => measurableSet_quotient.mpr
      ((show IsOpen s from hs).preimage continuous_quotient_mk').measurableSet)⟩
  have hcomp : ∀ i, KPContSectorFixedLineNormIntegrals.componentLineNorm F ζ hζ U R P H d i =ᵐ[
      KPFiniteCuspAtlas.quotientVolume F (Component F ζ hζ U R P H i)
        ((H.atlas U).cuspAtlas i).fundamentalDomain] 0 := by
    intro i
    haveI : OpensMeasurableSpace (KPCuspSiegel.OrbitQuotient F (Component F ζ hζ U R P H i)) :=
      ⟨MeasurableSpace.generateFrom_le (fun s hs => measurableSet_quotient.mpr
        ((show IsOpen s from hs).preimage continuous_quotient_mk').measurableSet)⟩
    have hpoint : (fun x : SymmetricSpace F =>
        KPContSectorFixedLineNormIntegrals.componentLineNorm F ζ hζ U R P H d i
          (KPCuspSiegel.projection F (Component F ζ hζ U R P H i) x)) =ᵐ[
          (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict
            ((H.atlas U).cuspAtlas i).fundamentalDomain] 0 := by
      filter_upwards [ae_restrict_of_ae (he i)] with x hx
      have hn : (S F ζ hζ U R P H d i).val x = 0 := by
        change (S F ζ hζ U R P H (f - g) i).val x = 0
        rw [map_sub]
        exact sub_eq_zero.mpr hx
      change ENNReal.ofReal (‖(S F ζ hζ U R P H d i).val x‖ ^ 2) = 0
      rw [hn]
      simp
    exact (ae_map_iff
      (show AEMeasurable (KPCuspSiegel.projection F (Component F ζ hζ U R P H i)) _ from
        measurable_quotient_mk''.aemeasurable)
      (measurableSet_eq_fun (N.component_borel i) measurable_const)).mpr hpoint
  have hi : ∫⁻ v, ENNReal.ofReal (‖d.val v‖ ^ 2) ∂coveredMeasure F ζ hζ R U = 0 := by
    have hp := N.restricted_pushforward Set.univ MeasurableSet.univ
    have hc := N.component_integral Set.univ MeasurableSet.univ
    simp only [Set.preimage_univ, Measure.restrict_univ] at hp hc
    rw [hp, hc]
    apply Finset.sum_eq_zero
    intro i _
    rw [lintegral_congr_ae (hcomp i)]
    change (H.disintegration U).componentWeight i * ∫⁻ _ : KPCuspSiegel.OrbitQuotient F
      (Component F ζ hζ U R P H i), (0 : ENNReal) ∂KPFiniteCuspAtlas.quotientVolume F
        (Component F ζ hζ U R P H i) ((H.atlas U).cuspAtlas i).fundamentalDomain = 0
    rw [lintegral_zero, mul_zero]
  have hz : (fun v => ENNReal.ofReal (‖d.val v‖ ^ 2)) =ᵐ[coveredMeasure F ζ hζ R U] 0 :=
    (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp (hd.norm.pow_const 2))).mp hi
  filter_upwards [hz] with v hv
  have hnorm : ‖d.val v‖ ^ 2 = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hv) (sq_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))

private theorem patchedScalar_ae (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (s : ℂ) (hs : s ∈ Ω) (f : BorelL2Scalars F ζ hζ U R)
    (hf : scalarEmbedding F ζ hζ U R P H f = u s) :
    (scalarRepresentative F ζ hζ U R P H
      (patchedSmoothSections F ζ hζ U R P H Ω u locals s hs).val).val =ᵐ[coveredMeasure F ζ hζ R U] f.val.val := by
  let w := patchedSmoothSections F ζ hζ U R P H Ω u locals s hs
  apply scalar_ae_of_component_ae F ζ hζ U R P H _ f.val
    ((borel_iff F ζ hζ U R P H w.val).mp (fun i => (w.property i).continuous.measurable)) f.property.1
  intro i
  have he := patchedComponent_ae F ζ hζ U R P H Ω u locals s hs f hf i
  rw [scalarRepresentative_eq_symm, LinearEquiv.apply_symm_apply]
  exact he

private theorem patched_represents (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (s : ℂ) (hs : s ∈ Ω) : Represents F ζ hζ U R P H
      (patchedSmoothSections F ζ hζ U R P H Ω u locals s hs).val (u s) := by
  obtain ⟨f,hf⟩ := scalarEmbedding_surjective F ζ hζ U R P H (u s)
  have he := patchedScalar_ae F ζ hζ U R P H Ω u locals s hs f hf
  have hm := MemLp.ae_eq he.symm f.property.2
  refine ⟨hm, ?_⟩
  exact (MemLp.toLp_congr _ _ he).trans ((scalarEmbedding_coe F ζ hζ U R P H f).symm.trans
    (congrArg (fun v : KPContSectorClosedLpSubspace.H F ζ hζ R U =>
      (v : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U)) hf))

private theorem smooth_represents_unique (w w' : smoothSections F ζ hζ U R P H)
    (v : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (hw : Represents F ζ hζ U R P H w.val v) (hw' : Represents F ζ hζ U R P H w'.val v) : w = w' := by
  letI := (levelSupport F ζ hζ R P
    (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1 U).covered_open_positive
  obtain ⟨hf,hh⟩ := hw
  obtain ⟨hg,hg'⟩ := hw'
  have hae := (hf.toLp_eq_toLp_iff hg).mp (hh.trans hg'.symm)
  have hc := (continuous_iff F ζ hζ U R P H w.val).mp (fun i => (w.property i).continuous)
  have hd := (continuous_iff F ζ hζ U R P H w'.val).mp (fun i => (w'.property i).continuous)
  have he := (hc.ae_eq_iff_eq (coveredMeasure F ζ hζ R U) hd).mp hae
  apply Subtype.ext
  exact (S F ζ hζ U R P H).symm.injective (Subtype.ext he)

theorem localRepresentatives_gluing (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u) :
    Nonempty (Gluing F ζ hζ U R P H Ω u locals) := by
  let W : ℂ → smoothSections F ζ hζ U R P H := fun s =>
    if hs : s ∈ Ω then patchedSmoothSections F ζ hζ U R P H Ω u locals s hs else 0
  have hW : ∀ s (hs : s ∈ Ω), W s = patchedSmoothSections F ζ hζ U R P H Ω u locals s hs := by
    intro s hs
    exact dif_pos hs
  refine ⟨{ representative := W
            coefficients := ?_
            represents := ?_
            unique := ?_
            group_lift := ?_ }⟩
  · intro s hs A
    rw [hW s hs]
    exact patchedSmoothSections_coefficients F ζ hζ U R P H Ω u locals s hs A
  · intro s hs
    rw [hW s hs]
    exact patched_represents F ζ hζ U R P H Ω u locals s hs
  · intro s hs w hw
    apply Subtype.ext
    apply section_ext F ζ hζ U R P H
    intro A
    apply (hw A).trans
    rw [hW s hs]
    exact (patchedSmoothSections_coefficients F ζ hζ U R P H Ω u locals s hs A).symm
  · intro s hs a c
    exact group_lift_formula F ζ hζ U _ a c

private theorem derivativeList_eqOn {n : ℕ} {B : LocalBall n}
    {f g : Space n → ℂ} (h : Set.EqOn f g B.carrier) (l : List (Fin n)) :
    Set.EqOn (coordinateDerivativeList l f) (coordinateDerivativeList l g) B.carrier := by
  induction l with
  | nil => exact h
  | cons i l ih =>
    intro x hx
    have he : coordinateDerivativeList l f =ᶠ[𝓝 x] coordinateDerivativeList l g :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx) (fun y hy => ih hy)
    change fderiv ℝ (coordinateDerivativeList l f) x (EuclideanSpace.single i 1) =
      fderiv ℝ (coordinateDerivativeList l g) x (EuclideanSpace.single i 1)
    rw [he.fderiv_eq]

theorem chartHolomorphic_congr {n : ℕ} (B : LocalBall n) (Ω : Set ℂ)
    (f g : ℂ → Space n → ℂ)
    (hf : KPCutoffSource.ChartSmoothHolomorphicOn B f Ω)
    (he : ∀ s ∈ Ω, Set.EqOn (g s) (f s) B.carrier) :
    KPCutoffSource.ChartSmoothHolomorphicOn B g Ω := by
  refine ⟨fun s hs => (hf.1 s hs).congr (he s hs), ?_⟩
  intro K hK hKB m
  obtain ⟨j, hj, hv⟩ := hf.2 K hK hKB m
  refine ⟨j, hj, ?_⟩
  intro s hs α x
  exact (hv s hs α x).trans ((derivativeList_eqOn (he s hs) α.directions (hKB x.property)).symm)

theorem smoothPowerSeries_congr {n : ℕ} (B : LocalBall n) (c : ℂ) (r : ℝ)
    (b d : ℕ → Space n → ℂ) (f g : ℂ → Space n → ℂ)
    (hf : SmoothPowerSeriesOn B c r b f)
    (hb : ∀ j, Set.EqOn (d j) (b j) B.carrier)
    (hg : ∀ s ∈ Metric.ball c r, Set.EqOn (g s) (f s) B.carrier) :
    SmoothPowerSeriesOn B c r d g := by
  refine ⟨fun j => (hf.1 j).congr (hb j), fun s hs => (hf.2.1 s hs).congr (hg s hs), ?_⟩
  intro K hK hKB m ρ hρ hρr ε hε
  obtain ⟨N, hN⟩ := hf.2.2 K hK hKB m ρ hρ hρr ε hε
  refine ⟨N, ?_⟩
  intro M hM s hs α x
  have he : Set.EqOn
      (fun y => (∑ j ∈ Finset.range M, (s - c) ^ j * d j y) - g s y)
      (fun y => (∑ j ∈ Finset.range M, (s - c) ^ j * b j y) - f s y) B.carrier := by
    intro y hy
    dsimp only
    rw [hg s (Metric.closedBall_subset_ball hρr hs) hy]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hb j hy]
  have hd := derivativeList_eqOn he α.directions (hKB x.property)
  change ‖coordinateDerivativeList α.directions _ _‖ < ε
  rw [hd]
  exact hN M hM s hs α x

theorem hasLocalPromotions_holomorphic (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (glued : Gluing F ζ hζ U R P H Ω u locals)
    (h : HasLocalPromotions F ζ hζ U R P H Ω u locals) :
    ∀ A : ChartBall F ζ hζ U R P H,
      KPCutoffSource.ChartSmoothHolomorphicOn A.ball
        (fun s => coefficient F ζ hζ U R P H (glued.representative s).val A) Ω := by
  intro A
  obtain ⟨p, hp⟩ := h A
  apply chartHolomorphic_congr A.ball Ω p.representative _ p.holomorphic
  intro s hs x hx
  exact (glued.coefficients s hs A hx).trans (hp s hs hx).symm

theorem hasLocalPromotions_coefficientLocals (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (h : HasLocalPromotions F ζ hζ U R P H Ω u locals)
    (c : ℂ) (r : ℝ) (hr : 0 < r) (hdisk : Metric.closedBall c r ⊆ Ω) :
    ∃ (b : ChartBall F ζ hζ U R P H → ℕ → Space (KPCuspLogShape.dimension F * 3) → ℂ)
      (L : ∀ j, LocalRepresentatives F ζ hζ U R P H Set.univ
        (fun _ => (cauchyPowerSeries u c r j) (fun _ => 1))),
      (∀ A j s, (L j).coefficient A s = b A j) ∧
      (∀ A, SmoothPowerSeriesOn A.ball c r (b A) (locals.coefficient A)) ∧
      (∀ A j, b A j =ᵐ[volume.restrict A.ball.carrier]
        (fun p => restriction F ζ hζ U R P H A.component A.center A.chart A.phase
          A.ball A.contained ((cauchyPowerSeries u c r j) (fun _ => 1)) p)) ∧
      (∀ A j (f : Space (KPCuspLogShape.dimension F * 3) → ℂ),
        ContDiffOn ℝ (⊤ : ℕ∞) f A.ball.carrier →
        (f =ᵐ[volume.restrict A.ball.carrier]
          (fun p => restriction F ζ hζ U R P H A.component A.center A.chart A.phase
            A.ball A.contained ((cauchyPowerSeries u c r j) (fun _ => 1)) p)) →
        Set.EqOn f (b A j) A.ball.carrier) := by
  choose promotion hpromotion using h
  choose b hb hseries hunique using fun A => (promotion A).disks c r hr hdisk
  let L : ∀ j, LocalRepresentatives F ζ hζ U R P H Set.univ
      (fun _ => (cauchyPowerSeries u c r j) (fun _ => 1)) := fun j =>
    { coefficient := fun A _ => b A j
      smooth := fun A _ _ => (hseries A).1 j
      represents := fun A _ _ => hb A j }
  refine ⟨b, L, fun _ _ _ => rfl, ?_, hb, hunique⟩
  intro A
  apply smoothPowerSeries_congr A.ball c r (b A) (b A)
    (promotion A).representative (locals.coefficient A) (hseries A)
  · intro j x hx
    rfl
  · intro s hs
    exact (hpromotion A s (hdisk (Metric.ball_subset_closedBall hs))).symm

theorem coefficientSeries_transfer (Ω : Set ℂ)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (glued : Gluing F ζ hζ U R P H Ω u locals)
    (c : ℂ) (r : ℝ) (hdisk : Metric.closedBall c r ⊆ Ω)
    (b : ChartBall F ζ hζ U R P H → ℕ → Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (hseries : ∀ A, SmoothPowerSeriesOn A.ball c r (b A) (locals.coefficient A))
    (W : ℕ → smoothSections F ζ hζ U R P H)
    (hW : ∀ A j, Set.EqOn (coefficient F ζ hζ U R P H (W j).val A) (b A j) A.ball.carrier) :
    ∀ A, SmoothPowerSeriesOn A.ball c r
      (fun j => coefficient F ζ hζ U R P H (W j).val A)
      (fun s => coefficient F ζ hζ U R P H (glued.representative s).val A) := by
  intro A
  apply smoothPowerSeries_congr A.ball c r (b A) _ (locals.coefficient A) _ (hseries A)
  · exact hW A
  · intro s hs
    exact glued.coefficients s (hdisk (Metric.ball_subset_closedBall hs)) A

theorem hasLocalPromotions_holomorphicData (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (locals : LocalRepresentatives F ζ hζ U R P H Ω u)
    (glued : Gluing F ζ hζ U R P H Ω u locals) :
    HasLocalPromotions F ζ hζ U R P H Ω u locals →
      HolomorphicData F ζ hζ U R P H Ω u glued.representative := by
  intro h
  refine ⟨hasLocalPromotions_holomorphic F ζ hζ U R P H Ω u locals glued h, ?_⟩
  intro c r hr hdisk
  obtain ⟨b, L, hL, hseries, hb, hunique⟩ :=
    hasLocalPromotions_coefficientLocals F ζ hζ U R P H Ω u locals h c r hr hdisk
  let B := fun j => patchedSmoothSections F ζ hζ U R P H Set.univ
    (fun _ => (cauchyPowerSeries u c r j) (fun _ => 1)) (L j) 0 (Set.mem_univ _)
  have hB : ∀ A j, Set.EqOn (coefficient F ζ hζ U R P H (B j).val A)
      (b A j) A.ball.carrier := by
    intro A j x hx
    exact (patchedSmoothSections_coefficients F ζ hζ U R P H Set.univ
      (fun _ => (cauchyPowerSeries u c r j) (fun _ => 1)) (L j) 0
      (Set.mem_univ _) A hx).trans (congrFun (hL A j 0) x)
  have hrep : ∀ j, Represents F ζ hζ U R P H (B j).val
      ((cauchyPowerSeries u c r j) (fun _ => 1)) := by
    intro j
    exact patched_represents F ζ hζ U R P H Set.univ
      (fun _ => (cauchyPowerSeries u c r j) (fun _ => 1)) (L j) 0 (Set.mem_univ _)
  refine ⟨B, hrep, ?_, coefficientSeries_transfer F ζ hζ U R P H Ω u locals
    glued c r hdisk b hseries B hB, ?_⟩
  · intro j w hw
    exact smooth_represents_unique F ζ hζ U R P H w (B j) _ hw (hrep j)
  · intro A j f hf hfae
    exact (hunique A j f hf hfae).trans (hB A j).symm

end DedekindZetaZeroFree.KPContActualSmoothLineGluing

namespace DedekindZetaZeroFree

theorem kp_cont_actual_smooth_line_gluing
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualSmoothLineGluing.Contract F ζ hζ U R P H :=
  ⟨KPContActualSmoothLineGluing.separation_of_realization F ζ hζ U R P H realization,
    fun Ω hΩ u locals =>
      KPContActualSmoothLineGluing.localRepresentatives_gluing F ζ hζ U R P H Ω hΩ u locals,
    fun Ω hΩ u locals glued h =>
      KPContActualSmoothLineGluing.hasLocalPromotions_holomorphicData
        F ζ hζ U R P H Ω hΩ u locals glued h⟩

end DedekindZetaZeroFree

end
