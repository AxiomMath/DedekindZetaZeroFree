module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSectors.CutoffMultipliers
public import DedekindZetaZeroFree.Analysis.ContinuousLinearMaps.DenseBoundedExtension
public import DedekindZetaZeroFree.Analysis.FunctionalAnalysis.DenseLinearExtension

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualFormCutoffClosedProduct

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings
open KPContActualSectorTestDifferentialDescent KPContActualSquareEndPartition
open KPContActualCotangentMeasurableFamilies KPContCotangentOverlapRationalBranches
open KPContActualSectorCotangentL2 KPContActualCotangentIntrinsicHilbertIntegral
open KPContActualCotangentCountableShrinking

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

local notation "D" => KPContActualSectorFriedrichsSynthesis.A_U
  F ζ hζ U R P H μG hμG hR realization
local notation "𝓗" => KPContSectorClosedLpSubspace.H F ζ hζ R U
local notation "𝓥" => KPContActualSectorCotangentL2.V F ζ hζ U R P H

include μG hμG hR realization

 theorem graphTest_mem (f : S_U F ζ hζ U R P H) :
    WithLp.toLp 2 (iota f, j (D_U f)) ∈ closedGradientGraph D := by
  change (iota f, j (D_U f)) ∈ (D).closure.graph
  apply LinearPMap.le_graph_of_le (D).le_closure
  have hg := (D).mem_graph ⟨iota f, LinearMap.mem_range_self iota f⟩
  simpa only [KPContActualSectorFriedrichsSynthesis.A_U,
    KPTestOperator.descend_image] using hg

def graphTestLift (f : S_U F ζ hζ U R P H) : ClosedGradientSpace D :=
  ⟨WithLp.toLp 2 (iota f, j (D_U f)),
    graphTest_mem F ζ hζ U R P H μG hμG hR realization f⟩

def graphTestLinear : S_U F ζ hζ U R P H →ₗ[ℂ] ClosedGradientSpace D where
  toFun f := graphTestLift F ζ hζ U R P H μG hμG hR realization f
  map_add' f g := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    simp [graphTestLift, map_add, WithLp.toLp_add, WithLp.ofLp_add, WithLp.ofLp_toLp]
  map_smul' c f := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    simp [graphTestLift, map_smul, WithLp.toLp_smul, WithLp.ofLp_smul, WithLp.ofLp_toLp]

private theorem fst_embedding (w : ClosedGradientSpace D) :
    closedGradientEmbedding D w = (WithLp.ofLp (w : WithLp 2 (𝓗 × 𝓥))).1 := by
  simp [closedGradientEmbedding, WithLp.fstL]

private theorem closedGradientEmbedding_graphTestLift (f : S_U F ζ hζ U R P H) :
    closedGradientEmbedding D (graphTestLift F ζ hζ U R P H μG hμG hR realization f)
      = iota f := by
  rw [fst_embedding F ζ hζ U R P H μG hμG hR realization]
  simp [graphTestLift, WithLp.ofLp_toLp]

private theorem closedGradientEmbedding_graphTestLinear (f : S_U F ζ hζ U R P H) :
    closedGradientEmbedding D (graphTestLinear F ζ hζ U R P H μG hμG hR realization f)
      = iota f := by
  rw [show graphTestLinear F ζ hζ U R P H μG hμG hR realization f
    = graphTestLift F ζ hζ U R P H μG hμG hR realization f from rfl]
  exact closedGradientEmbedding_graphTestLift F ζ hζ U R P H μG hμG hR realization f

private theorem graphTestLinear_dense :
    DenseRange (graphTestLinear F ζ hζ U R P H μG hμG hR realization) := by
  intro w
  rw [mem_closure_iff_seq_limit]
  have hprops := kp_cont_actual_sector_friedrichs_synthesis F ζ hζ μG hμG U R hR P H realization
  have hemb := closedGradientEmbedding_properties D hprops.gradient_dense hprops.gradient_closable
  have hmem : (WithLp.linearEquiv 2 ℂ (𝓗 × 𝓥)) (w : WithLp 2 (𝓗 × 𝓥)) ∈ (D).closure.graph :=
    w.property
  obtain ⟨hv, hvv⟩ := (D).closure.mem_graph_iff.mp hmem
  rw [WithLp.coe_linearEquiv] at hvv
  have hfd : closedGradientEmbedding D w = (WithLp.ofLp (w : WithLp 2 (𝓗 × 𝓥))).1 :=
    fst_embedding F ζ hζ U R P H μG hμG hR realization w
  have hu : closedGradientEmbedding D w ∈ (D).closure.domain := by
    rw [hfd, ← hvv.1]
    exact hv.property
  obtain ⟨s, hs1, hs2, -⟩ := hprops.form_core ⟨closedGradientEmbedding D w, hu⟩
  refine ⟨fun n => graphTestLinear F ζ hζ U R P H μG hμG hR realization (s n),
    fun n => ⟨s n, rfl⟩, ?_⟩
  rw [tendsto_subtype_rng]
  have hw : (w : WithLp 2 (𝓗 × 𝓥)) =
      WithLp.toLp 2 (closedGradientEmbedding D w,
        (D).closure ⟨closedGradientEmbedding D w, hu⟩) := by
    apply WithLp.ofLp_injective
    rw [WithLp.ofLp_toLp]
    apply Prod.ext
    · exact hfd.symm
    · rw [← hvv.2]
      congr 1
      exact Subtype.ext (hvv.1.trans hfd.symm)
  rw [hw]
  have hpair : Filter.Tendsto (fun n => (iota (s n), j (D_U (s n)))) Filter.atTop
      (nhds ((closedGradientEmbedding D w),
        (D).closure ⟨closedGradientEmbedding D w, hu⟩)) := hs1.prodMk_nhds hs2
  refine ((WithLp.prod_continuous_toLp 2 𝓗 𝓥).tendsto _).comp hpair

private theorem j_norm_sq (η : RealSmoothCutoff F ζ hζ U R P H) (f : S_U F ζ hζ U R P H) :
    ‖j (cutoffGradientTimes η f)‖ ^ 2 =
      ∫ x, (normSquare (cutoffGradientTimes η f).val x : ℝ)
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
  have hV := kp_cont_actual_sector_cotangent_l2 F ζ hζ μG hμG U R hR P H realization
  have h := hV.norm_integral (j (cutoffGradientTimes η f))
    (cotangentSquareFamily (cutoffGradientTimes η f)) rfl
  simpa [cotangentSquareFamily] using h

private theorem iota_norm_sq (f : S_U F ζ hζ U R P H) :
    ‖iota f‖ ^ 2 =
      ∫ x, (scalarPair f f x).re ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
  have hE := kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H realization
  have hint := hE.scalar_pair_integrable f f
  have hstep : (∫ x, (scalarPair f f x).re
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) =
      ∫ x, Complex.reCLM (scalarPair f f x)
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
    simp [Complex.reCLM_apply]
  rw [hstep, ContinuousLinearMap.integral_comp_comm Complex.reCLM hint,
    ← hE.scalar_inner f f, Complex.reCLM_apply]
  have hz : inner ℂ (iota f) (iota f) = ((‖iota f‖ : ℂ)) ^ 2 :=
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (iota f)
  rw [hz, ← Complex.ofReal_pow, Complex.ofReal_re]

private theorem normSquare_cutoffGradientTimes_le
    (η : RealSmoothCutoff F ζ hζ U R P H) (D₀ : ℝ) (hD₀ : 0 ≤ D₀)
    (hdη : ∀ (a : ActualChart (U := U) (H := H))
      (y : KPContCotangentOverlapRationalBranches.omega a),
      ‖cutoffDifferential η a y‖ ≤ D₀)
    (f : S_U F ζ hζ U R P H) (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ((normSquare (cutoffGradientTimes η f).val x : ℝ≥0) : ℝ) ≤
      D₀ ^ 2 * (scalarPair f f x).re := by
  have hE := kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H realization
  obtain ⟨cov⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  have hcov : ∀ x : KPFiniteCuspAtlas.rawXU F ζ hζ U,
      ∃ n, x ∈ (cov.chart n).baseDomain := by
    intro x
    have h := cov.covers
    rw [Set.eq_univ_iff_forall] at h
    simpa [Set.mem_iUnion] using h x
  obtain ⟨n, hn⟩ := hcov x
  obtain ⟨y, hy⟩ := hn
  let x' : KPContCotangentActualOverlap.M F :=
    KPContCotangentActualOverlap.labeledAInv
      (KPContCotangentActualOverlap.placeEquiv F ζ hζ) y.val
  have hx' : KPContCotangentActualOverlap.labeledA
      (KPContCotangentActualOverlap.placeEquiv F ζ hζ) x' = y.val := by
    funext k
    show (CotangentLogCoframe.A (KPContCotangentActualOverlap.d F))
        ((CotangentLogCoframe.A (KPContCotangentActualOverlap.d F)).symm
          (fun k' => y.val (KPContCotangentActualOverlap.placeEquiv F ζ hζ k')))
        ((KPContCotangentActualOverlap.placeEquiv F ζ hζ).symm k) = y.val k
    rw [ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hmem : x' ∈ omega (cov.chart n) := by
    show KPContCotangentActualOverlap.labeledA
      (KPContCotangentActualOverlap.placeEquiv F ζ hζ) x' ∈ (cov.chart n).domain
    rw [hx']; exact y.property
  let x'' : omega (cov.chart n) := ⟨x', hmem⟩
  have hqx : q (cov.chart n) x''.val = x := by
    rw [← hy]
    unfold KPContCotangentOverlapRationalBranches.q ShrunkChart.toBase
    rw [hx']
  rw [← hqx, normSquare_chart (cutoffGradientTimes η f).val (cov.chart n) x'']
  have hsp : (scalarPair f f (q (cov.chart n) x''.val)).re
      = ‖f.val (cov.chart n) x''‖ ^ 2 := by
    rw [hE.scalar_pair_chart f f (cov.chart n) x'']
    have hz : inner ℂ (f.val (cov.chart n) x'') (f.val (cov.chart n) x'')
        = ((‖f.val (cov.chart n) x''‖ : ℂ)) ^ 2 :=
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _
    rw [hz, ← Complex.ofReal_pow, Complex.ofReal_re]
  have hns : ((‖coefficient (cutoffGradientTimes η f).val (cov.chart n) x''‖₊ ^ 2
        : ℝ≥0) : ℝ)
      = ‖f.val (cov.chart n) x''‖ ^ 2
        * ‖cutoffDifferential η (cov.chart n) x''‖ ^ 2 := by
    have hc : coefficient (cutoffGradientTimes η f).val (cov.chart n) x''
        = f.val (cov.chart n) x'' • cutoffDifferential η (cov.chart n) x'' := rfl
    have hcoe : ((‖coefficient (cutoffGradientTimes η f).val (cov.chart n) x''‖₊ ^ 2
        : ℝ≥0) : ℝ) = ‖coefficient (cutoffGradientTimes η f).val (cov.chart n) x''‖ ^ 2 := by
      rw [NNReal.coe_pow]
      rfl
    rw [hcoe, hc, norm_smul]
    ring
  rw [hns, hsp]
  have h1 : ‖cutoffDifferential η (cov.chart n) x''‖ ^ 2 ≤ D₀ ^ 2 := by
    nlinarith [hdη (cov.chart n) x'',
      norm_nonneg (cutoffDifferential η (cov.chart n) x''), hD₀]
  nlinarith [h1, sq_nonneg ‖f.val (cov.chart n) x''‖]

private theorem cutoffGradientTimes_norm_bound
    (η : RealSmoothCutoff F ζ hζ U R P H) (D₀ : ℝ) (hD₀ : 0 ≤ D₀)
    (hdη : ∀ (a : ActualChart (U := U) (H := H))
      (y : KPContCotangentOverlapRationalBranches.omega a),
      ‖cutoffDifferential η a y‖ ≤ D₀)
    (f : S_U F ζ hζ U R P H) :
    ‖j (cutoffGradientTimes η f)‖ ≤ D₀ * ‖iota f‖ := by
  have hE := kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H realization
  have hint := hE.scalar_pair_integrable f f
  have hW : Integrable
      (fun x => ((normSquare (cutoffGradientTimes η f).val x : ℝ≥0) : ℝ))
      (KPContActualSectorCotangentL2.muU F ζ hζ U R P) :=
    KPContActualCotangentIntrinsicHilbertIntegral.integrable_normSquare
      (cotangentSquareFamily (cutoffGradientTimes η f))
  have h2 : Integrable (fun x => D₀ ^ 2 * (scalarPair f f x).re)
      (KPContActualSectorCotangentL2.muU F ζ hζ U R P) :=
    hint.re.const_mul _
  have hmain : ‖j (cutoffGradientTimes η f)‖ ^ 2 ≤ D₀ ^ 2 * ‖iota f‖ ^ 2 := by
    rw [j_norm_sq F ζ hζ U R P H μG hμG hR realization η f,
      iota_norm_sq F ζ hζ U R P H μG hμG hR realization f]
    calc ∫ x, ((normSquare (cutoffGradientTimes η f).val x : ℝ≥0) : ℝ)
          ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P
        ≤ ∫ x, D₀ ^ 2 * (scalarPair f f x).re
          ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P :=
          integral_mono hW h2 (fun x => normSquare_cutoffGradientTimes_le F ζ hζ U R P H μG hμG
            hR realization η D₀ hD₀ hdη f x)
      _ = D₀ ^ 2 * ∫ x, (scalarPair f f x).re
          ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P :=
          integral_const_mul _ _
  have hsq : (D₀ * ‖iota f‖) ^ 2 = D₀ ^ 2 * ‖iota f‖ ^ 2 := by ring
  nlinarith [hmain, hsq, norm_nonneg (j (cutoffGradientTimes η f)),
    mul_nonneg hD₀ (norm_nonneg (iota f))]

private theorem exists_scalar_to_cotangent
    (η : RealSmoothCutoff F ζ hζ U R P H) (D₀ : ℝ) (hD₀ : 0 ≤ D₀)
    (hdη : ∀ (a : ActualChart (U := U) (H := H))
      (y : KPContCotangentOverlapRationalBranches.omega a),
      ‖cutoffDifferential η a y‖ ≤ D₀) :
    ∃ C : 𝓗 →L[ℂ] 𝓥, ‖C‖ ≤ D₀ ∧
      ∀ f : S_U F ζ hζ U R P H, C (iota f) = j (cutoffGradientTimes η f) := by
  have hdense := KPContActualSectorFriedrichsSynthesis.scalarDense
    F ζ hζ U R P H μG hμG hR realization
  have hbound : ∀ f : S_U F ζ hζ U R P H,
      ‖(j.comp (cutoffGradientTimes η)) f‖ ≤ D₀ * ‖iota f‖ :=
    fun f => cutoffGradientTimes_norm_bound F ζ hζ U R P H μG hμG hR realization
      η D₀ hD₀ hdη f
  refine ⟨LinearMap.extendOfNorm (σ₁₂ := RingHom.id ℂ)
    ((j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)).comp (cutoffGradientTimes η))
    (iota (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)), ?_, ?_⟩
  · exact LinearMap.opNorm_extendOfNorm_le hdense hD₀ hbound
  · intro f
    exact LinearMap.extendOfNorm_eq hdense ⟨D₀, hbound⟩ f

private theorem graphTestLinear_bound
    (η : RealSmoothCutoff F ζ hζ U R P H) (M : SectorMultiplier F ζ hζ U R P H η)
    (B D₀ : ℝ) (hB : 0 ≤ B) (hD₀ : 0 ≤ D₀)
    (hη : ∀ x, |η.val x| ≤ B)
    (hdη : ∀ (a : ActualChart (U := U) (H := H))
      (y : KPContCotangentOverlapRationalBranches.omega a),
      ‖cutoffDifferential η a y‖ ≤ D₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : S_U F ζ hζ U R P H,
      ‖graphTestLinear F ζ hζ U R P H μG hμG hR realization (scalarMultiply η f)‖
        ≤ K * ‖graphTestLinear F ζ hζ U R P H μG hμG hR realization f‖ := by
  obtain ⟨C, hCnorm, hCeq⟩ := exists_scalar_to_cotangent F ζ hζ U R P H μG hμG hR realization
    η D₀ hD₀ hdη
  obtain ⟨N, hNnorm, hNeq⟩ := KPContActualCotangentBoundedScalarMultiplier.exists_multiplier
    F ζ hζ U R P H μG hμG hR realization η B hB hη
  have hdp := fun f => (kp_cont_actual_sector_test_differential_descent F ζ hζ μG hμG U R hR P H
    realization).differential_product η f
  have hM0 : (0 : ℝ) ≤ ‖M.op‖ := ContinuousLinearMap.opNorm_nonneg M.op
  refine ⟨‖M.op‖ + B + D₀, add_nonneg (add_nonneg hM0 hB) hD₀, ?_⟩
  intro f
  have hnormsq : ∀ g : S_U F ζ hζ U R P H,
      ‖graphTestLinear F ζ hζ U R P H μG hμG hR realization g‖ ^ 2
        = ‖iota g‖ ^ 2 + ‖j (D_U g)‖ ^ 2 := by
    intro g
    have hv : (graphTestLinear F ζ hζ U R P H μG hμG hR realization g :
        WithLp 2 (𝓗 × 𝓥)) = WithLp.toLp 2 (iota g, j (D_U g)) := rfl
    rw [show ‖graphTestLinear F ζ hζ U R P H μG hμG hR realization g‖
        = ‖(graphTestLinear F ζ hζ U R P H μG hμG hR realization g : WithLp 2 (𝓗 × 𝓥))‖
        from rfl, hv, WithLp.prod_norm_sq_eq_of_L2]
    simp
  set a : ℝ := ‖iota f‖ with ha
  set b : ℝ := ‖j (D_U f)‖ with hb
  have ha0 : 0 ≤ a := by rw [ha]; exact norm_nonneg _
  have hb0 : 0 ≤ b := by rw [hb]; exact norm_nonneg _
  set G : ℝ := ‖graphTestLinear F ζ hζ U R P H μG hμG hR realization f‖ with hG
  have hG0 : 0 ≤ G := by rw [hG]; exact norm_nonneg _
  have hG2 : G ^ 2 = a ^ 2 + b ^ 2 := by rw [hG, hnormsq f, ha, hb]
  have haG : a ≤ G := by nlinarith [ha0, hb0, hG2]
  have hbG : b ≤ G := by nlinarith [ha0, hb0, hG2]
  have hgrad : j (D_U (scalarMultiply η f)) = N (j (D_U f)) + C (iota f) := by
    rw [hdp f, map_add, hNeq (D_U f), hCeq f]
  have hX : ‖iota (scalarMultiply η f)‖ ≤ ‖M.op‖ * G := by
    rw [← M.test_commutes f]
    exact le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_left haG (norm_nonneg _))
  have hY : ‖j (D_U (scalarMultiply η f))‖ ≤ (B + D₀) * G := by
    rw [hgrad]
    calc ‖N (j (D_U f)) + C (iota f)‖ ≤ ‖N (j (D_U f))‖ + ‖C (iota f)‖ := norm_add_le _ _
      _ ≤ ‖N‖ * b + ‖C‖ * a := by
          rw [hb, ha]
          exact add_le_add (ContinuousLinearMap.le_opNorm _ _)
            (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ B * G + D₀ * G :=
          add_le_add (mul_le_mul hNnorm hbG hb0 hB) (mul_le_mul hCnorm haG ha0 hD₀)
      _ = (B + D₀) * G := by ring
  have hX2 : ‖iota (scalarMultiply η f)‖ ^ 2 ≤ (‖M.op‖ * G) ^ 2 := by
    nlinarith [hX, norm_nonneg (iota (scalarMultiply η f)), hG0, norm_nonneg M.op]
  have hY2 : ‖j (D_U (scalarMultiply η f))‖ ^ 2 ≤ ((B + D₀) * G) ^ 2 := by
    nlinarith [hY, norm_nonneg (j (D_U (scalarMultiply η f))), hG0, hB, hD₀]
  have hKG : (‖M.op‖ * G) ^ 2 + ((B + D₀) * G) ^ 2
      ≤ ((‖M.op‖ + B + D₀) * G) ^ 2 := by
    nlinarith [sq_nonneg G, norm_nonneg M.op, hB, hD₀,
      mul_nonneg (norm_nonneg M.op) (add_nonneg hB hD₀)]
  have hgoal : ‖graphTestLinear F ζ hζ U R P H μG hμG hR realization (scalarMultiply η f)‖
      ≤ (‖M.op‖ + B + D₀) * G := by
    have hsq : ‖graphTestLinear F ζ hζ U R P H μG hμG hR realization (scalarMultiply η f)‖ ^ 2
        ≤ ((‖M.op‖ + B + D₀) * G) ^ 2 := by
      rw [hnormsq (scalarMultiply η f)]
      linarith [hX2, hY2, hKG]
    have h2 : 0 ≤ (‖M.op‖ + B + D₀) * G :=
      mul_nonneg (add_nonneg (add_nonneg hM0 hB) hD₀) hG0
    have h3 := sq_le_sq.mp hsq
    rw [abs_of_nonneg h2] at h3
    simpa using h3
  exact hgoal

theorem exists_lift
    (η : RealSmoothCutoff F ζ hζ U R P H)
    (M : SectorMultiplier F ζ hζ U R P H η)
    (B D₀ : ℝ) (hB : 0 ≤ B) (hD₀ : 0 ≤ D₀)
    (hη : ∀ x, |η.val x| ≤ B)
    (hdη : ∀ (a : ActualChart (U := U) (H := H))
      (y : KPContCotangentOverlapRationalBranches.omega a),
      ‖cutoffDifferential η a y‖ ≤ D₀) :
    ∃ A : ClosedGradientSpace D →L[ℂ] ClosedGradientSpace D,
      (closedGradientEmbedding D).comp A =
        M.op.comp (closedGradientEmbedding D) ∧
      ∀ f : S_U F ζ hζ U R P H,
        A (graphTestLift F ζ hζ U R P H μG hμG hR realization f) =
          graphTestLift F ζ hζ U R P H μG hμG hR realization (scalarMultiply η f) := by
  obtain ⟨K, hK0, hbound⟩ := graphTestLinear_bound F ζ hζ U R P H μG hμG hR realization
    η M B D₀ hB hD₀ hη hdη
  have hclosable : (D).IsClosable :=
    (kp_cont_actual_sector_friedrichs_synthesis F ζ hζ μG hμG U R hR P H
      realization).gradient_closable
  haveI hNS : NormedSpace ℂ (ClosedGradientSpace D) :=
    Submodule.normedSpace (closedGradientGraph D)
  haveI hBS : IsBoundedSMul ℂ (ClosedGradientSpace D) :=
    IsBoundedSMul.of_norm_smul_le
      (fun c x => norm_smul_le c (x : WithLp 2 (𝓗 × 𝓥)))
  haveI hCS : CompleteSpace (ClosedGradientSpace D) :=
    (closedGradientGraph_isClosed D hclosable).completeSpace_coe
  have hdenseE : DenseRange (graphTestLinear F ζ hζ U R P H μG hμG hR realization) :=
    graphTestLinear_dense F ζ hζ U R P H μG hμG hR realization
  set L : ClosedGradientSpace D →L[ℂ] ClosedGradientSpace D :=
    LinearMap.extendOfNorm (σ₁₂ := RingHom.id ℂ)
      ((graphTestLinear F ζ hζ U R P H μG hμG hR realization).comp (scalarMultiply η))
      (graphTestLinear F ζ hζ U R P H μG hμG hR realization) with hLdef
  have hLeq : ∀ f : S_U F ζ hζ U R P H,
      L (graphTestLinear F ζ hζ U R P H μG hμG hR realization f)
        = graphTestLinear F ζ hζ U R P H μG hμG hR realization (scalarMultiply η f) := by
    intro f
    rw [hLdef]
    exact LinearMap.extendOfNorm_eq hdenseE ⟨K, hbound⟩ f
  have hLproj : (closedGradientEmbedding D).comp L
      = M.op.comp (closedGradientEmbedding D) := by
    apply DFunLike.coe_injective
    refine DenseRange.equalizer hdenseE ((closedGradientEmbedding D).comp L).continuous
      (M.op.comp (closedGradientEmbedding D)).continuous ?_
    funext f
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hLeq f,
      closedGradientEmbedding_graphTestLinear F ζ hζ U R P H μG hμG hR realization
        (scalarMultiply η f),
      closedGradientEmbedding_graphTestLinear F ζ hζ U R P H μG hμG hR realization f]
    exact (M.test_commutes f).symm
  refine ⟨L, hLproj, fun f => ?_⟩
  show L (graphTestLinear F ζ hζ U R P H μG hμG hR realization f)
      = graphTestLinear F ζ hζ U R P H μG hμG hR realization (scalarMultiply η f)
  exact hLeq f

end DedekindZetaZeroFree.KPContActualFormCutoffClosedProduct

end
