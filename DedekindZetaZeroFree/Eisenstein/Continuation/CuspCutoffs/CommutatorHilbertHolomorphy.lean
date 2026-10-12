module

public import DedekindZetaZeroFree.Analysis.Holomorphy.CompactCharts.ClosedRangeRestriction

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCommutatorHilbertHolomorphy

open KPContActualCutoffSmoothDescent
open KPContSectorCoveredQuotientVocabulary KPContSectorFixedPushforwardSupport
open KPContSectorSmoothFramesSupport KPContSectorScalarLineAlgebra

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {T : ℝ}
variable (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)

def compactDomain : KPContActualCompactSectorL2Map.CompactDomain F ζ hζ
    (level F ζ hζ C R P H U) R where
  compact := ⟨KPContActualCollarBuffer.coveredCollars F ζ hζ
    (level F ζ hζ C R P H U) R P H B.τ T, B.compact_covered_collars⟩
  measurable := by
    letI : BorelSpace (KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ
      (level F ζ hζ C R P H U)) := ⟨rfl⟩
    exact B.compact_covered_collars.isClosed.measurableSet
  finite_measure := B.finite_covered_measure
  central_invariant := by
    intro ε x
    change x ∈ KPContActualCollarBuffer.coveredCollars F ζ hζ
        (level F ζ hζ C R P H U) R P H B.τ T ↔
      z F ζ hζ (level F ζ hζ C R P H U) ε x ∈
        KPContActualCollarBuffer.coveredCollars F ζ hζ
          (level F ζ hζ C R P H U) R P H B.τ T
    simp only [KPContActualCollarBuffer.coveredCollars, Set.mem_preimage]
    rw [KPContSectorCoveredQuotientVocabulary.q_z]

abbrev ScalarSpace := KPContActualCompactSectorL2Map.E_L F ζ hζ
  (level F ζ hζ C R P H U) R (compactDomain F ζ hζ C R P H U B)

abbrev HilbertSpace := KPContSectorClosedLpSubspace.H F ζ hζ R
  (level F ζ hζ C R P H U)

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (Ω : Set ℂ) (f : ℂ → S)
variable (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (D : Descent F ζ hζ C R P H U ι B Ω f χ)

structure Conclusions where
  g : ℂ → ScalarSpace F ζ hζ C R P H U B
  restriction : ∀ s ∈ Ω, ∀ x : (compactDomain F ζ hζ C R P H U B).compact,
    (g s).val x = scalar F ζ hζ C R P H U (D.commutator s) x.val
  off_domain : ∀ s ∉ Ω, g s = 0
  scalar_holomorphic : DifferentiableOn ℂ g Ω
  J_L : ScalarSpace F ζ hζ C R P H U B →L[ℂ] HilbertSpace F ζ hζ C R P H U
  extension_bound : ‖J_L‖ ≤ Real.sqrt
    ((coveredMeasure F ζ hζ R (level F ζ hζ C R P H U)).real
      (compactDomain F ζ hζ C R P H U B).compact)
  zero_extension : ∀ v : ScalarSpace F ζ hζ C R P H U B,
    (((J_L v : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R
      (level F ζ hζ C R P H U)) : Covered F ζ hζ C R P H U → ℂ) =ᵐ[
        coveredMeasure F ζ hζ R (level F ζ hζ C R P H U)]
      KPContActualCompactSectorL2Map.zeroExtension F ζ hζ
        (level F ζ hζ C R P H U) R (compactDomain F ζ hζ C R P H U B) v)
  hilbert_holomorphic : DifferentiableOn ℂ (fun s => J_L (g s)) Ω
  inclusion : ∀ s ∈ Ω,
    (((J_L (g s) : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R
      (level F ζ hζ C R P H U)) : Covered F ζ hζ C R P H U → ℂ) =ᵐ[
        coveredMeasure F ζ hζ R (level F ζ hζ C R P H U)]
      scalar F ζ hζ C R P H U (D.commutator s))

  representative : ∀ s ∈ Ω, ∃ b : KPContSectorLineL2Isometry.BorelL2Scalars F ζ hζ
      (level F ζ hζ C R P H U) R,
    b.val.val = scalar F ζ hζ C R P H U (D.commutator s) ∧
    KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ
      (level F ζ hζ C R P H U) R P H (J_L (g s)) =
        KPContSectorLineL2Isometry.mk F ζ hζ (level F ζ hζ C R P H U) R P H
          (KPContSectorLineL2Isometry.borelS F ζ hζ (level F ζ hζ C R P H U) R P H b) ∧
    (KPContSectorLineL2Isometry.borelS F ζ hζ (level F ζ hζ C R P H U) R P H b).val =
      (D.commutator s).val ∧
    (∀ i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount,
      ∀ q : KPContActualCutoffChartJetHolomorphy.Chart F ζ hζ C R P H U i,
      ∀ x ∈ KPContActualCutoffChartJetHolomorphy.chartDomain F ζ hζ C R P H U q,
        q.coefficient
          (KPContSectorLineL2Isometry.borelS F ζ hζ (level F ζ hζ C R P H U) R P H b).val
          (KPContActualCutoffChartJetHolomorphy.coordinates F x) =
        KPContActualCutoffChartJetHolomorphy.framePullback F ζ hζ C R P H U q
          (D.commutator s) x)

end DedekindZetaZeroFree.KPContActualCommutatorHilbertHolomorphy

namespace DedekindZetaZeroFree

theorem kp_cont_actual_commutator_hilbert_holomorphy
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (_hR : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H)
    {T : ℝ} (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H T)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (hι : Function.Injective ι)
    (_hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (Ω : Set ℂ) (hΩopen : IsOpen Ω) (hΩ : Ω ⊆ KPContinuation.spectralDomain)
    (f : ℂ → S) (hf : DifferentiableOn ℂ f Ω)
    (χ : KPContActualCutoffSmoothDescent.Cusps F ζ hζ C R P H U →
      KPCutoffSource.SmoothCuspCutoff T)
    (D : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι B Ω f χ) :
    Nonempty (KPContActualCommutatorHilbertHolomorphy.Conclusions
      F ζ hζ C R P H U B ι Ω f χ D) := by
  let L := KPContActualCommutatorHilbertHolomorphy.compactDomain F ζ hζ C R P H U B
  let v (s : ℂ) : KPContActualCommutatorHilbertHolomorphy.ScalarSpace F ζ hζ C R P H U B :=
    ⟨⟨fun x => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
        (D.commutator s) x.val,
      ((KPContSectorLineL2Isometry.continuous_iff F ζ hζ
        (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H
        (D.commutator s).val).mp
          (fun i => ((D.commutator s).property i).continuous)).comp continuous_subtype_val⟩,
      by
        intro ε x
        exact ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
          (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H).symm
            (D.commutator s)).val.property ε x.val⟩
  let g (s : ℂ) := if s ∈ Ω then v s else 0
  have hg (s : ℂ) (hs : s ∈ Ω) : g s = v s := if_pos hs
  have hrestrict (s : ℂ) (hs : s ∈ Ω) (x : L.compact) :
      (g s).val x = KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
        (D.commutator s) x.val := by rw [hg s hs]; rfl
  have hext (s : ℂ) (hs : s ∈ Ω) :
      KPContActualCompactSectorL2Map.zeroExtension F ζ hζ
        (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R L (g s) =
          KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (D.commutator s) := by
    funext x
    by_cases hx : x ∈ L.compact
    · simpa only [KPContActualCompactSectorL2Map.zeroExtension, dif_pos hx] using
        hrestrict s hs ⟨x, hx⟩
    · change (if hx : x ∈ L.compact then (g s).val ⟨x, hx⟩ else 0) = _
      rw [dif_neg hx]
      symm
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => hx (D.covered_support s hs h)
  have hhol : DifferentiableOn ℂ g Ω := by
    let A := (CompactChartRestriction.finiteChartCover_exists F ζ hζ C R P H U L _hR).some
    let T := CompactChartRestriction.frameRestrictionIsometry F ζ hζ C R P H U L A
    apply CompactChartRestriction.isometry_differentiableOn T
      (CompactChartRestriction.frameRestriction_closedRange F ζ hζ C R P H U L A) g Ω hΩopen
    apply differentiableOn_pi.mpr
    intro j
    by_cases hK : Nonempty (A.piece j)
    · obtain ⟨x⟩ := hK
      have hcontained : (A.piece j : Set (KPContLocalNorm.Space
          (KPContActualCutoffChartJetHolomorphy.dimension F))) ⊆
          KPContActualCutoffChartJetHolomorphy.chartDomain F ζ hζ C R P H U (A.chart j) := by
        intro y hy
        have hy' := hy
        rw [A.piece_eq] at hy'
        exact A.outer_contained j hy'.1
      have hcoord : Continuous (KPContActualCutoffChartJetHolomorphy.coordinates F) := by
        unfold KPContActualCutoffChartJetHolomorphy.coordinates
        apply Continuous.comp (PiLp.continuous_toLp (p := (2 : ℝ≥0∞)) (fun _ : Fin (KPContCotangentActualOverlap.d F) × Fin 3 => ℝ))
        exact continuous_pi (fun ik => (EuclideanSpace.proj (finProdFinEquiv ik)).continuous)
      have hopen : IsOpen (KPContActualCutoffChartJetHolomorphy.chartDomain
          F ζ hζ C R P H U (A.chart j)) :=
        (A.chart j).isOpen_omega.preimage hcoord
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x.val (hcontained x.property)
      let ball : KPContLocalNorm.LocalBall (KPContActualCutoffChartJetHolomorphy.dimension F) :=
        { center := x.val, radius := r / 2, radius_pos := by positivity
          dimension_pos := by
            have hd := KPCuspLogShape.dimension_pos F H.totallyComplex
            have he := (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.1
            change 0 < KPContCotangentActualOverlap.d F * 3
            have hp : 0 < KPContCotangentActualOverlap.d F := by
              simpa only [KPContCotangentActualOverlap.d, ← B.dimension_formula] using hd
            omega }
      have hj := kp_cont_actual_cutoff_chart_jet_holomorphy F ζ hζ C R P H U _hR B
        ι hι _hStage Ω hΩ hΩopen f hf χ D (A.component j) (A.chart j) ball
        ((Metric.closedBall_subset_ball (by dsimp [ball]; linarith)).trans hball)
      obtain ⟨jet, hjet, hformula, _⟩ := hj.compact_jets true (A.piece j) (A.piece j).isCompact
        hcontained 0
      let α : KPContLocalNorm.MultiIndex (KPContActualCutoffChartJetHolomorphy.dimension F) 0 :=
        ⟨fun _ => 0, by simp⟩
      have hzero (u : KPContLocalNorm.Space (KPContActualCutoffChartJetHolomorphy.dimension F) → ℂ) :
          KPContLocalNorm.coordinateDerivative α u = u := by
        have hnil : ∀ l : List (Fin (KPContActualCutoffChartJetHolomorphy.dimension F)),
            l.flatMap (fun _ => ([] : List (Fin (KPContActualCutoffChartJetHolomorphy.dimension F)))) = [] := by
          intro l
          induction l with
          | nil => rfl
          | cons a l ih => simpa using ih
        simp [α, KPContLocalNorm.coordinateDerivative, KPContLocalNorm.MultiIndex.directions,
          KPContLocalNorm.coordinateDerivativeList, hnil]
      have hcomp := (ContinuousLinearMap.proj α).differentiable.comp_differentiableOn hjet
      apply hcomp.congr
      intro s hs
      ext y
      rw [CompactChartRestriction.frameRestriction_smooth F ζ hζ C R P H U L A
        (D.commutator s) (g s) (hrestrict s hs)]
      change _ = jet s α y
      simpa only [hzero, KPContActualCutoffChartJetHolomorphy.pullback, Bool.true_eq_false,
        ite_false, ite_true] using (hformula s hs α y).symm
    · letI : IsEmpty (A.piece j) := not_nonempty_iff.mp hK
      have he : (fun s => T (g s) j) = fun _ => 0 := by
        funext s
        ext x
        exact isEmptyElim x
      rw [he]
      exact differentiableOn_const _
  obtain ⟨J, hbound, hJ⟩ := kp_cont_actual_compact_sector_l2_map F ζ hζ
    (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H _hR L
  refine ⟨{
    g := g
    restriction := hrestrict
    off_domain := fun s hs => if_neg hs
    scalar_holomorphic := hhol
    J_L := J
    extension_bound := hbound
    zero_extension := fun w => (hJ w).2.2.1
    hilbert_holomorphic := J.differentiable.comp_differentiableOn hhol
    inclusion := ?_
    representative := ?_ }⟩
  · intro s hs
    simpa only [hext s hs] using (hJ (g s)).2.2.1
  · intro s hs
    obtain ⟨b, hb, _, hline, _⟩ := (hJ (g s)).2.2.2.2
    have hbscalar : b.val = ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
        (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H).symm
          (D.commutator s)).val := Subtype.ext (hb.trans (hext s hs))
    have hsections : (KPContSectorLineL2Isometry.borelS F ζ hζ
        (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H b).val =
          (D.commutator s).val := by
      change KPContSectorScalarLineAlgebra.S F ζ hζ
        (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H b.val = _
      rw [hbscalar]
      exact congrArg Subtype.val
        ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
          (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H).apply_symm_apply
            (D.commutator s))
    refine ⟨b, hb.trans (hext s hs), hline, hsections, ?_⟩
    intro i q x hx
    rw [hsections]
    rfl

end DedekindZetaZeroFree

end
