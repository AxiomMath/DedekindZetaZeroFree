module

public import DedekindZetaZeroFree.Adeles.Quotients.GreenIdentities.InteriorZeroExtension
public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.EquivariantScalarAndCotangentData
public import DedekindZetaZeroFree.Analysis.Sobolev.WeightedCovariant.CoordinateData

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings
open KPContActualSectorTestDifferentialDescent KPContActualSectorChartEquivariantInputs
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches KPContLocalNorm

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable {μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)} {hμG : μG.IsHaarMeasure}
variable {hR : R.adelicHaar = μG}
variable {realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H}

section FirstJetHelpers
open scoped ContDiff
open KPContActualCotangentChartRestriction
open KPContCotangentActualGenuineTwistIsotropy
section Canonical
open KPContSectorCoveredQuotientVocabulary KPContSectorQuotientRelationsComparison
open KPContSectorFixedPushforwardSupport KPContSectorScalarLineAlgebra
open KPContSectorSmoothFramesSupport KPMsFixedHaarDisintegration
set_option maxHeartbeats 2000000 in
 theorem canonicalRealization :
    KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H := by
  refine
    { actual_projection := rfl
      quotient_projection := (piTilde_isOpenMap F ζ hζ U).isQuotientMap
        (piTilde_continuous F ζ hζ U) (piTilde_surjective F ζ hζ U)
      covered_pushforward := rfl
      support := levelSupport F ζ hζ R P ((KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1) U
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

end Canonical
private theorem base_direction (j : Fin (3*d F)) :
    (baseReindex (F:=F)).symm (EuclideanSpace.single j 1) =
      HyperbolicChart.coordinateVector (d F) ((coefficientIndex (F:=F)).symm j).1
        ((coefficientIndex (F:=F)).symm j).2 := by
  ext ik
  simp only [baseReindex, LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.symm_symm, HyperbolicChart.coordinateVector,
    WithLp.ofLp_toLp]
  simp [EuclideanSpace.single_apply, Pi.single_apply, ← Equiv.apply_eq_iff_eq_symm_apply]
private theorem flat_derivative (g : M F → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : Space (3*d F)) (j : Fin (3*d F)) :
    KPCompactInteriorH1.coordinatePartial j (fun y => g ((baseReindex (F:=F)).symm y)) x =
      HyperbolicChart.coordinateDerivative (d F) ((coefficientIndex (F:=F)).symm j).1
        ((coefficientIndex (F:=F)).symm j).2 g ((baseReindex (F:=F)).symm x) := by
  unfold KPCompactInteriorH1.coordinatePartial
  have hd := ((hg.differentiable (by simp) _).hasFDerivAt.comp x
    ((baseReindex (F:=F)).symm.toContinuousLinearEquiv.hasFDerivAt)).fderiv
  change fderiv ℝ (g ∘ (baseReindex (F:=F)).symm) x _ = _
  change fderiv ℝ (g ∘ (baseReindex (F:=F)).symm) x = _ at hd
  rw [hd, ContinuousLinearMap.comp_apply]
  rw [show KPCompactInteriorH1.coordinateDirection j = EuclideanSpace.single j 1 from rfl]
  change fderiv ℝ g _ ((baseReindex (F:=F)).symm _) = _
  rw [base_direction]
  rfl
private theorem smooth_flat (a : ActualChart (U := U) (H := H)) (f : localScalarTests a)
    (L : Set (Space (3*d F))) (hL : IsCompact L)
    (hLω : L ⊆ (baseReindex (F:=F)).symm ⁻¹' omega a)
    (hs : tsupport (fun x => liftExtension a f.val ((baseReindex (F:=F)).symm x)) ⊆ L) :
    ContDiff ℝ (⊤ : ℕ∞) (liftExtension a f.val) := by
  apply KPContActualGlobalGreen.interior_liftExtension_contDiff a f.val f.property.1
  have ht := tsupport_comp_eq_preimage (liftExtension a f.val) (baseReindex (F:=F)).toHomeomorph.symm
  change tsupport (fun y => liftExtension a f.val ((baseReindex (F:=F)).symm y)) = _ at ht
  intro x hx
  have hx' : baseReindex x ∈ tsupport (fun y => liftExtension a f.val ((baseReindex (F:=F)).symm y)) := by
    rw [ht]
    simpa using hx
  simpa using hLω (hs hx')
private theorem coframe_bound (g : M F → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : Space (3*d F)) (C : ℝ) (hC : 1 ≤ C)
    (hbound : ∀ i : Fin (d F), Real.exp (2 * ((baseReindex (F:=F)).symm x) (i,2)) ≤ C) :
    ‖CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) g ((baseReindex (F:=F)).symm x))‖ ^ 2 ≤
      C * ∑ j : Fin (3*d F), ‖KPCompactInteriorH1.coordinatePartial j
        (fun y => g ((baseReindex (F:=F)).symm y)) x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp_rw [CotangentLogCoframe.j_apply]
  conv_rhs => rw [← Equiv.sum_comp (coefficientIndex (F:=F)), Fintype.sum_prod_type]
  simp_rw [flat_derivative g hg]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Fin.sum_univ_three, Fin.sum_univ_three, HyperbolicChart.differential]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow]
  have he : Real.exp (((baseReindex (F:=F)).symm x) (i,2)) ^ 2 =
      Real.exp (2 * ((baseReindex (F:=F)).symm x) (i,2)) := by rw [← Real.exp_nat_mul]; norm_num
  simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_def, Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.cons_val_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  rw [he]
  have h0 := mul_le_mul_of_nonneg_right (hbound i) (sq_nonneg
    (‖HyperbolicChart.coordinateDerivative (d F) i 0 g ((baseReindex (F:=F)).symm x)‖))
  have h1 := mul_le_mul_of_nonneg_right (hbound i) (sq_nonneg
    (‖HyperbolicChart.coordinateDerivative (d F) i 1 g ((baseReindex (F:=F)).symm x)‖))
  have h2 := mul_le_mul_of_nonneg_right hC (sq_nonneg
    (‖HyperbolicChart.coordinateDerivative (d F) i 2 g ((baseReindex (F:=F)).symm x)‖))
  nlinarith

open KPContActualSectorTestEmbeddings KPContActualCotangentMeasurableFamilies
open KPContActualCotangentChartRestriction KPContActualCotangentPieceHilbertSum
private theorem base_point (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ (a : ActualChart (U := U) (H := H)) (y : omega a), q a y.val = x := by
  let C := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  have hx : x ∈ ⋃ n, (C.chart n).baseDomain := by rw [C.covers]; trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y, hy⟩ := hn
  refine ⟨C.chart n, coordinates (C.chart n) y, ?_⟩
  have hi : ∀ z : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
    intro z; funext k; simp [labeledA, labeledAInv]
  rw [← hy]
  simp only [KPContCotangentOverlapRationalBranches.q, coordinates, KPContActualCotangentCountableShrinking.ShrunkChart.toBase]
  rw [hi]
private theorem pair_support (v w : Family (U := U) (H := H)) :
    tsupport (pair v w) ⊆ cotangentSupport w := by
  refine closure_mono (fun x hx => ?_)
  obtain ⟨a, y, hy⟩ := base_point x
  refine ⟨a, y, hy, ?_⟩
  have hpx : pair v w (q a y.val) ≠ 0 := by rw [hy]; exact hx
  rw [pair_chart] at hpx
  intro hw
  exact hpx (by rw [hw, inner_zero_right])
private theorem norm_integrals (a : ActualChart (U:=U) (H:=H)) (f : localScalarTests a) :
    ‖iota (scalarZeroExtension a f)‖ ^ 2 = ∫ y, ‖f.val (coordinates a y)‖ ^ 2 ∂a.liftedMeasure ∧
    ‖j (D_U (scalarZeroExtension a f))‖ ^ 2 =
      ∫ y, ‖chartDifferential a f.val (coordinates a y)‖ ^ 2 ∂a.liftedMeasure := by
  let re : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H := canonicalRealization
  have ps := kp_cont_actual_sector_smooth_test_modules F ζ hζ R.adelicHaar R.adelic_isHaar U R rfl P H re
  have pd := kp_cont_actual_sector_test_differential_descent F ζ hζ R.adelicHaar R.adelic_isHaar U R rfl P H re
  let u := scalarZeroExtension a f
  have hu : u.val a = f.val := ps.scalar_restriction_extension a f
  have hs : scalarSupport u.val ⊆ a.baseDomain := by
    rw [ps.scalar_extension_support]
    exact f.property.2.2.2
  have hd : cotangentSupport (D_U u).val ⊆ a.baseDomain := (pd.differential_support u).trans hs
  constructor
  · have he := scalar_inner re u u
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := a.baseDomain) (fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun ht => hx (hs (tsupport_scalarPair_subset u u ht)))), scalar_chart_integral a u u] at he
    have hc : inner ℂ (iota u) (iota u) = ((‖iota u‖ ^ 2 : ℝ) : ℂ) := by
      convert (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (iota u)) using 1 <;> norm_cast
    have hi : (∫ y, inner ℂ (localScalarCoefficient a u y) (localScalarCoefficient a u y) ∂a.liftedMeasure) =
        ((∫ y, ‖localScalarCoefficient a u y‖ ^ 2 ∂a.liftedMeasure : ℝ) : ℂ) := by
      convert (integral_ofReal (f := fun y => ‖localScalarCoefficient a u y‖ ^ 2) (μ := a.liftedMeasure)) using 1
      congr 1; funext y
      convert (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _) using 1 <;> norm_cast
    rw [hc, hi] at he
    have hre : ‖iota u‖ ^ 2 = ∫ y, ‖localScalarCoefficient a u y‖ ^ 2 ∂a.liftedMeasure := by
      exact_mod_cast he
    refine hre.trans ?_
    apply integral_congr_ae
    filter_upwards with y
    change ‖u.val a (coordinates a y)‖ ^ 2 = _
    rw [hu]
  · have he := cotangent_inner re (D_U u) (D_U u)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := a.baseDomain) (fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun ht => hx (hd (pair_support _ _ ht)))), cotangent_chart_integral a (D_U u) (D_U u)] at he
    have hc : inner ℂ (j (D_U u)) (j (D_U u)) = ((‖j (D_U u)‖ ^ 2 : ℝ) : ℂ) := by
      convert (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (j (D_U u))) using 1 <;> norm_cast
    have hi : (∫ y, inner ℂ (localCoefficient a (D_U u).val y) (localCoefficient a (D_U u).val y) ∂a.liftedMeasure) =
        ((∫ y, ‖localCoefficient a (D_U u).val y‖ ^ 2 ∂a.liftedMeasure : ℝ) : ℂ) := by
      convert (integral_ofReal (f := fun y => ‖localCoefficient a (D_U u).val y‖ ^ 2) (μ := a.liftedMeasure)) using 1
      congr 1; funext y
      convert (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _) using 1 <;> norm_cast
    rw [hc, hi] at he
    have hre : ‖j (D_U u)‖ ^ 2 = ∫ y, ‖localCoefficient a (D_U u).val y‖ ^ 2 ∂a.liftedMeasure := by
      exact_mod_cast he
    refine hre.trans ?_
    apply integral_congr_ae
    filter_upwards with y
    change ‖coefficient (D_U u).val a (coordinates a y)‖ ^ 2 = _
    rw [pd.differential_chart, hu]

private theorem weighted_finite (a : ActualChart (U:=U) (H:=H))
    (L : Set (Space (3*d F))) (hL : IsCompact L)
    (hLω : L ⊆ (baseReindex (F:=F)).symm ⁻¹' omega a) :
    KPChartL2.weightedMeasure (3*d F) (chart a) (weight a) L < ⊤ := by
  have hsub : L ⊆ chart a := hLω
  rw [KPChartL2.weightedMeasure, withDensity_apply _ hL.measurableSet,
    Measure.restrict_restrict hL.measurableSet, Set.inter_eq_left.mpr hsub]
  have hi := ((scalarData (a := a)).locally_integrable_weight.mono_set hsub).integrableOn_isCompact hL
  apply lt_of_le_of_lt _ hi.hasFiniteIntegral
  apply lintegral_mono
  intro x
  change ENNReal.ofReal (weight a x) ≤ ‖weight a x‖ₑ
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)
private theorem compact_integrable (a : ActualChart (U:=U) (H:=H))
    (L : Set (Space (3*d F))) (hL : IsCompact L)
    (hLω : L ⊆ (baseReindex (F:=F)).symm ⁻¹' omega a)
    (g : Space (3*d F) → ℝ) (hg : Continuous g) :
    IntegrableOn g L (KPChartL2.weightedMeasure (3*d F) (chart a) (weight a)) := by
  haveI : IsFiniteMeasure ((KPChartL2.weightedMeasure (3*d F) (chart a) (weight a)).restrict L) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (weighted_finite a L hL hLω)⟩
  obtain ⟨C,hC⟩ := hL.exists_bound_of_continuousOn hg.continuousOn
  apply Integrable.of_bound (hg.aestronglyMeasurable) C
  exact ae_restrict_of_forall_mem hL.measurableSet hC

end FirstJetHelpers

theorem scalarZeroExtension_firstJet_bound
    (a : ActualChart (U := U) (H := H)) (L : Set (Space (3 * d F)))
    (hL : IsCompact L) (hLω : L ⊆ (baseReindex (F := F)).symm ⁻¹' omega a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : localScalarTests a),
      tsupport (fun x : Space (3 * d F) =>
        liftExtension a f.val ((baseReindex (F := F)).symm x)) ⊆ L →
      ‖iota (scalarZeroExtension a f)‖ ^ 2 + ‖j (D_U (scalarZeroExtension a f))‖ ^ 2 ≤
        C * ∫ x in L, (‖liftExtension a f.val ((baseReindex (F := F)).symm x)‖ ^ 2
          + ∑ j : Fin (3 * d F),
              ‖KPCompactInteriorH1.coordinatePartial j
                (fun y : Space (3 * d F) =>
                  liftExtension a f.val ((baseReindex (F := F)).symm y)) x‖ ^ 2)
          ∂KPChartL2.weightedMeasure (3 * d F) (chart a) (weight a) := by
  have hb : ∀ i : Fin (d F), ∃ C : ℝ, ∀ x ∈ L,
      Real.exp (2 * ((baseReindex (F:=F)).symm x) (i,2)) ≤ C := by
    intro i
    obtain ⟨C,hC⟩ := hL.exists_bound_of_continuousOn
      (show Continuous (fun x : Space (3*d F) => Real.exp (2 * ((baseReindex (F:=F)).symm x) (i,2))) by fun_prop).continuousOn
    exact ⟨C, fun x hx => le_trans (le_abs_self _) (hC x hx)⟩
  choose B hB using hb
  let C := 1 + ∑ i, |B i|
  have hC : 1 ≤ C := by
    have hp := Finset.sum_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (B i))
    dsimp [C]; linarith
  have hbound : ∀ x ∈ L, ∀ i : Fin (d F), Real.exp (2 * ((baseReindex (F:=F)).symm x) (i,2)) ≤ C := by
    intro x hx i
    apply (hB i x hx).trans
    calc B i ≤ |B i| := le_abs_self _
      _ ≤ ∑ j, |B j| := Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_univ i)
      _ ≤ C := by dsimp [C]; linarith
  refine ⟨C, by linarith, ?_⟩
  intro f hs
  let g := liftExtension a f.val
  let gf := fun x => g ((baseReindex (F:=F)).symm x)
  let ν := KPChartL2.weightedMeasure (3*d F) (chart a) (weight a)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := smooth_flat a f L hL hLω hs
  have hgf : ContDiff ℝ (⊤ : ℕ∞) gf := hg.comp (baseReindex (F:=F)).symm.contDiff
  have hder (i : Fin (3*d F)) : ContDiff ℝ (⊤ : ℕ∞) (KPCompactInteriorH1.coordinatePartial i gf) :=
    (hgf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  let J := fun x => ‖gf x‖ ^ 2 + ∑ j, ‖KPCompactInteriorH1.coordinatePartial j gf x‖ ^ 2
  let V := fun x => ‖gf x‖ ^ 2
  let W := fun x => ‖CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) g ((baseReindex (F:=F)).symm x))‖ ^ 2
  have hV : Continuous V := hgf.continuous.norm.pow 2
  have hJ : Continuous J := hV.add (continuous_finset_sum _ fun j _ => (hder j).continuous.norm.pow 2)
  have hW : Continuous W := by
    dsimp [W]
    rw [show (fun x => ‖CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) g ((baseReindex (F:=F)).symm x))‖ ^ 2) =
      (fun x => ∑ i : Fin (d F), ∑ k : Fin 3, ‖HyperbolicChart.differential (d F) g ((baseReindex (F:=F)).symm x) i k‖ ^ 2) by
        funext x; rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]; simp only [CotangentLogCoframe.j_apply]]
    apply continuous_finset_sum
    intro i _
    simp only [Fin.sum_univ_three]
    have hd (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (HyperbolicChart.coordinateDerivative (d F) i k g) :=
      (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
    simp only [HyperbolicChart.differential, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.vecHead, Matrix.vecTail, Function.comp_def, Fin.succ_zero_eq_one]
    fun_prop
  have iV := compact_integrable a L hL hLω V hV
  have iJ := compact_integrable a L hL hLω J hJ
  have iW := compact_integrable a L hL hLω W hW
  have hv0 : ∀ x, x ∉ L → V x = 0 := by
    intro x hx
    have hz : gf x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
    simp [V, hz]
  have hw0 : ∀ x, x ∉ L → W x = 0 := by
    intro x hx
    have hzero (j : Fin (3*d F)) : KPCompactInteriorH1.coordinatePartial j gf x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro ht
      exact hx (hs ((tsupport_fderiv_apply_subset ℝ (KPCompactInteriorH1.coordinateDirection j)) ht))
    have hc := coframe_bound g hg x (1 + ∑ i, Real.exp (2 * ((baseReindex (F:=F)).symm x) (i,2)))
      (by
        have hp := Finset.sum_nonneg (s := Finset.univ) (fun i _ => (Real.exp_pos (2 * ((baseReindex (F:=F)).symm x) (i,2))).le)
        linarith) (fun i => by
        have hi := Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin (d F) => Real.exp (2 * ((baseReindex (F:=F)).symm x) (j,2)))
          (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
        linarith)
    change ‖CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) g ((baseReindex (F:=F)).symm x))‖ ^ 2 ≤
      _ * ∑ j, ‖KPCompactInteriorH1.coordinatePartial j gf x‖ ^ 2 at hc
    simp only [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero] at hc
    exact le_antisymm hc (sq_nonneg _)
  have eV := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ν) hv0
  have eW := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ν) hw0
  have transport (G : Space (3*d F) → ℝ) (hG : Continuous G) :
      (∫ x, G x ∂ν) = ∫ y : a.domain, G (fromActual (ζ := ζ) (hζ := hζ) y.val) ∂a.liftedMeasure := by
    dsimp [ν]
    rw [← lifted_measure_transport (a := a)]
    apply integral_map _ hG.aestronglyMeasurable
    have hm : Continuous (fun y : a.domain => fromActual (ζ := ζ) (hζ := hζ) y.val) := by
      unfold fromActual labeledAInv
      exact (baseReindex (F:=F)).continuous.comp ((CotangentLogCoframe.A (d F)).symm.continuous.comp
        (continuous_pi fun k => (continuous_apply _).comp continuous_subtype_val))
    exact hm.measurable.aemeasurable
  have hlocal := norm_integrals a f
  have mapV : (∫ y, ‖f.val (KPContActualCotangentPieceHilbertSum.coordinates a y)‖ ^ 2 ∂a.liftedMeasure) = ∫ x in L, V x ∂ν := by
    rw [eV, transport V hV]
    apply integral_congr_ae
    filter_upwards with y
    have hy : labeledAInv (placeEquiv F ζ hζ) y.val ∈ omega a := (KPContActualCotangentPieceHilbertSum.coordinates a y).property
    simp [V, gf, g, fromActual, KPContActualCotangentPieceHilbertSum.coordinates, liftExtension, hy]
  have mapW : (∫ y, ‖chartDifferential a f.val (KPContActualCotangentPieceHilbertSum.coordinates a y)‖ ^ 2 ∂a.liftedMeasure) = ∫ x in L, W x ∂ν := by
    rw [eW, transport W hW]
    apply integral_congr_ae
    filter_upwards with y
    simp only [W, g, chartDifferential, fromActual, LinearIsometryEquiv.symm_apply_apply]
    rfl
  rw [hlocal.1, hlocal.2, mapV, mapW, ← integral_add iV iW]
  rw [← integral_const_mul]
  apply integral_mono_ae (iV.add iW) (iJ.const_mul C)
  filter_upwards [ae_restrict_mem hL.measurableSet] with x hx
  have hc := coframe_bound g hg x C hC (hbound x hx)
  have hv : V x ≤ C * V x := by dsimp [V]; nlinarith [sq_nonneg ‖gf x‖]
  dsimp [J, V, W, gf] at *
  nlinarith

end DedekindZetaZeroFree

end
