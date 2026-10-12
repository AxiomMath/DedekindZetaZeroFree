module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GradientForms.CutoffJetBounds
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspForms.RadialComparison

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualFormLocalRestrictionCompact

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualFixedHaarCoreLocalizers
open KPContSectorLineL2Isometry
open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra
open KPContSectorFixedPushforwardSupport KPContSectorClosedLpSubspace

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

local notation "Q" => KPContActualCuspRadialFormComparison.Q_U F ζ hζ U R P H μG hμG hR realization
local notation "jU" => KPContActualCuspRadialFormComparison.j_U F ζ hζ U R P H μG hμG hR realization
local notation "qU" => KPContActualCuspRadialFormComparison.q_U F ζ hζ U R P H μG hμG hR realization
local notation "HU" => H_U F ζ hζ U R
local notation "ActualD" => KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization
local notation "ActualV" => KPContActualSectorCotangentL2.V F ζ hζ U R P H
local notation "BU" => KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ U R P H μG hμG hR realization

theorem actual_coreTest_dense :
    DenseRange (KPContActualFormCutoffClosedProduct.graphTestLinear F ζ hζ U R P H μG hμG hR realization) := by
  intro w
  rw [mem_closure_iff_seq_limit]
  have hprops := kp_cont_actual_sector_friedrichs_synthesis F ζ hζ μG hμG U R hR P H realization
  have hmem : (WithLp.linearEquiv 2 ℂ (HU × ActualV)) (w : WithLp 2 (HU × ActualV)) ∈ (ActualD).closure.graph := w.property
  obtain ⟨hv, hvv⟩ := (ActualD).closure.mem_graph_iff.mp hmem
  rw [WithLp.coe_linearEquiv] at hvv
  have hfd : closedGradientEmbedding ActualD w = (WithLp.ofLp (w : WithLp 2 (HU × ActualV))).1 := rfl
  have hu : closedGradientEmbedding ActualD w ∈ (ActualD).closure.domain := by
    rw [hfd, ← hvv.1]
    exact hv.property
  obtain ⟨s, hs1, hs2, -⟩ := hprops.form_core ⟨closedGradientEmbedding ActualD w, hu⟩
  refine ⟨fun n => KPContActualFormCutoffClosedProduct.graphTestLinear F ζ hζ U R P H μG hμG hR realization (s n),
    fun n => ⟨s n,rfl⟩, ?_⟩
  rw [tendsto_subtype_rng]
  have hw : (w : WithLp 2 (HU × ActualV)) =
      WithLp.toLp 2 (closedGradientEmbedding ActualD w,
        (ActualD).closure ⟨closedGradientEmbedding ActualD w, hu⟩) := by
    apply WithLp.ofLp_injective
    rw [WithLp.ofLp_toLp]
    apply Prod.ext
    · exact hfd.symm
    · rw [← hvv.2]
      congr 1
      exact Subtype.ext (hvv.1.trans hfd.symm)
  rw [hw]
  exact ((WithLp.prod_continuous_toLp 2 HU ActualV).tendsto _).comp (hs1.prodMk_nhds hs2)

private theorem gradient_adjoint_lift
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V) (hdense : Dense (D.domain : Set H)) (hclosable : D.IsClosable) :
    ∃ b : H →L[ℂ] ClosedGradientSpace D,
      (closedGradientEmbedding D).comp b = closedGradientResolvent D hclosable ∧ ‖b‖ ≤ 1 := by
  letI : CompleteSpace (ClosedGradientSpace D) := closedGradientSpace_complete D hclosable
  refine ⟨ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := ClosedGradientSpace D) (F := H)
    (closedGradientEmbedding D), rfl, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using closedGradientFriedrichsOperator_riesz_estimate D hdense hclosable f

instance form_complete : CompleteSpace Q :=
  (kp_cont_actual_sector_test_friedrichs F ζ hζ μG hμG U R hR P H realization).friedrichs.form_hilbert

theorem form_norm_sq (v : Q) : ‖v‖ ^ 2 = qU v + ‖jU v‖ ^ 2 := by
  change ‖v.val‖ ^ 2 = ‖v.val.snd‖ ^ 2 + ‖v.val.fst‖ ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2, add_comm]

theorem formLift_exists : ∃ b : HU →L[ℂ] Q, (jU).comp b = BU ∧ ‖b‖ ≤ 1 := by
  have hdense :
      Dense ((KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR
        realization).domain : Set (KPContSectorClosedLpSubspace.H F ζ hζ R U)) :=
    (kp_cont_actual_sector_test_friedrichs F ζ hζ μG hμG U R hR P H
      realization).friedrichs.gradient_dense
  have hclosable :
      (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR
        realization).IsClosable :=
    (kp_cont_actual_sector_test_friedrichs F ζ hζ μG hμG U R hR P H
      realization).friedrichs.gradient_closable
  obtain ⟨b, hb1, hb2⟩ := gradient_adjoint_lift
    (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization)
    hdense hclosable
  exact ⟨b, hb1, hb2⟩

def b_U : HU →L[ℂ] Q :=
  Classical.choose (formLift_exists F ζ hζ U R P H μG hμG hR realization)

theorem b_U_properties :
    (jU).comp (b_U F ζ hζ U R P H μG hμG hR realization) = BU ∧
      ‖b_U F ζ hζ U R P H μG hμG hR realization‖ ≤ 1 :=
  Classical.choose_spec (formLift_exists F ζ hζ U R P H μG hμG hR realization)

variable (K : Set (X_U F ζ hζ U)) (hK : IsCompact K)

section

attribute [-instance] QuotientModule.Quotient.topologicalSpace
local instance : TopologicalSpace (H_K F ζ hζ U R P H K) :=
  (instNormedAddCommGroupHK F ζ hζ U R P H K).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
local instance : AddCommMonoid (H_K F ζ hζ U R P H K) :=
  (instNormedAddCommGroupHK F ζ hζ U R P H K).toSeminormedAddCommGroup.toAddCommMonoid
local instance : TopologicalSpace (H_U F ζ hζ U R) :=
  (inferInstance : NormedAddCommGroup (H_U F ζ hζ U R)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

def r_K : Q →L[ℂ] H_K F ζ hζ U R P H K :=
  (res_K F ζ hζ U R P H K hK.measurableSet).comp (jU)

def ChartFactorization (A : Localizers F ζ hζ U R P H K hK) : Prop :=
  ∃ L : ∀ i : Fin A.count, Q →L[ℂ]
      KPCubeGraphRellich.GraphSpace (A.chart i).n (A.chart i).a,
    (∀ i, (KPCubeGraphRellich.projection (A.chart i).n (A.chart i).a).comp (L i) =
      (A.T i).comp (jU)) ∧
    r_K F ζ hζ U R P H μG hμG hR realization K hK =
      ∑ i : Fin A.count, (A.Rmap i).comp
        ((KPCubeGraphRellich.projection (A.chart i).n (A.chart i).a).comp (L i))

 theorem actual_jet_add (n : ℕ) (a : ℝ) (f g : KPCubeAverage.Space n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    KPCubeGraphRellich.smoothJet n a (f + g) (hf.add hg) =
      KPCubeGraphRellich.smoothJet n a f hf + KPCubeGraphRellich.smoothJet n a g hg := by
  open KPCubeGraphRellich KPCubeAverage in
    rw [smoothJet, smoothJet, smoothJet, WithLp.ext_iff]
    simp only [WithLp.ofLp_toLp, WithLp.ofLp_add, Prod.mk_add_mk]
    refine Prod.ext ?_ ?_
    · rw [← MemLp.toLp_add (smooth_memLp n a f hf) (smooth_memLp n a g hg)]
    · rw [← WithLp.toLp_add, WithLp.ext_iff, WithLp.ofLp_toLp]
      funext j
      simp only [Pi.add_apply]
      rw [← MemLp.toLp_add (smooth_coordinate_memLp n a f hf j)
        (smooth_coordinate_memLp n a g hg j)]
      apply MemLp.toLp_congr
      apply Filter.EventuallyEq.of_eq
      funext x
      simp only [coordinateDerivative, Pi.add_apply]
      rw [fderiv_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x),
        ContinuousLinearMap.add_apply]

 theorem actual_jet_smul (n : ℕ) (a : ℝ) (f : KPCubeAverage.Space n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℂ) :
    KPCubeGraphRellich.smoothJet n a (c • f) (hf.const_smul c) =
      c • KPCubeGraphRellich.smoothJet n a f hf := by
  open KPCubeGraphRellich KPCubeAverage in
    rw [smoothJet, smoothJet, WithLp.ext_iff]
    simp only [WithLp.ofLp_toLp, WithLp.ofLp_smul, Prod.smul_mk]
    refine Prod.ext ?_ ?_
    · rw [← MemLp.toLp_const_smul c (smooth_memLp n a f hf)]
    · rw [← WithLp.toLp_smul, WithLp.ext_iff, WithLp.ofLp_toLp]
      funext j
      simp only [Pi.smul_apply]
      rw [← MemLp.toLp_const_smul c (smooth_coordinate_memLp n a f hf j)]
      apply MemLp.toLp_congr
      apply Filter.EventuallyEq.of_eq
      funext x
      simp only [coordinateDerivative, Pi.smul_apply]
      rw [fderiv_const_smul (hf.differentiable (by simp) x) c, ContinuousLinearMap.smul_apply]

 theorem actual_jet_congr (n : ℕ) (a : ℝ) (f g : KPCubeAverage.Space n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (h : f = g) :
    KPCubeGraphRellich.smoothJet n a f hf = KPCubeGraphRellich.smoothJet n a g hg := by
  subst g
  rfl

 theorem actualLocalCoefficient_add (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count)
    (f g : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H) :
    actualLocalCoefficient F ζ hζ U R P H K hK A i (f + g) =
      actualLocalCoefficient F ζ hζ U R P H K hK A i f +
        actualLocalCoefficient F ζ hζ U R P H K hK A i g := by
  funext x
  simp only [actualLocalCoefficient, map_add, Pi.add_apply, Submodule.coe_add]
  exact mul_add _ _ _

 theorem actualLocalCoefficient_smul (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count)
    (c : ℂ) (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H) :
    actualLocalCoefficient F ζ hζ U R P H K hK A i (c • f) =
      c • actualLocalCoefficient F ζ hζ U R P H K hK A i f := by
  funext x
  simp only [actualLocalCoefficient, map_smul, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul]
  ring

def actualCoreJet (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count) :
    KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H →ₗ[ℂ]
      KPCubeGraphRellich.GraphSpace (A.chart i).n (A.chart i).a where
  toFun f := ⟨KPCubeGraphRellich.smoothJet (A.chart i).n (A.chart i).a
    (actualLocalCoefficient F ζ hζ U R P H K hK A i f)
    (actualLocalCoefficient_smooth F ζ hζ U R P H μG hμG hR realization K hK A i f),
      Submodule.le_topologicalClosure _ ((KPCubeGraphRellich.mem_smoothSubspace_iff _ _ _).mpr ⟨_,_,rfl⟩)⟩
  map_add' f g := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    have hf := actualLocalCoefficient_smooth F ζ hζ U R P H μG hμG hR realization K hK A i f
    have hg := actualLocalCoefficient_smooth F ζ hζ U R P H μG hμG hR realization K hK A i g
    exact (actual_jet_congr _ _ _ _ _ (hf.add hg)
      (actualLocalCoefficient_add F ζ hζ U R P H K hK A i f g)).trans
        (actual_jet_add _ _ _ _ hf hg)
  map_smul' c f := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    have hf := actualLocalCoefficient_smooth F ζ hζ U R P H μG hμG hR realization K hK A i f
    exact (actual_jet_congr _ _ _ _ _ (hf.const_smul c)
      (actualLocalCoefficient_smul F ζ hζ U R P H K hK A i c f)).trans
        (actual_jet_smul _ _ _ hf c)

include μG hμG hR realization in
private theorem actual_test_representative (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H) :
    ∃ s : BorelL2Sections F ζ hζ U R P H,
      sectorLineIsometry F ζ hζ U R P H (KPContActualSectorTestEmbeddings.iota f) = mk F ζ hζ U R P H s ∧
      s.val = KPContActualSectorSmoothTestModules.scalarSections f := by
  have hprops := kp_cont_actual_sector_smooth_test_modules F ζ hζ μG hμG U R hR P H realization
  have hcont := (kp_cont_actual_sector_test_friedrichs F ζ hζ μG hμG U R hR P H realization).embeddings.scalar_continuous f
  let fB : BorelL2Scalars F ζ hζ U R := ⟨KPContActualSectorSmoothTestModules.scalarCovered f, hcont.measurable, KPContActualSectorTestEmbeddings.scalar_memLp f⟩
  let s := borelS F ζ hζ U R P H fB
  refine ⟨s, ?_, ?_⟩
  · have he : scalarEmbedding F ζ hζ U R P H fB = KPContActualSectorTestEmbeddings.iota f := by
      apply Subtype.ext
      rw [scalarEmbedding_coe]
      rfl
    rw [← he]
    exact sectorLineIsometry_toSector F ζ hζ U R P H fB
  · exact hprops.covered_realization f

private theorem actualCoreJet_projection_test (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count)
    (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H) :
    (KPCubeAverage.smooth_memLp (A.chart i).n (A.chart i).a
      (actualLocalCoefficient F ζ hζ U R P H K hK A i f)
      (actualLocalCoefficient_smooth F ζ hζ U R P H μG hμG hR realization K hK A i f)).toLp _ = A.T i (KPContActualSectorTestEmbeddings.iota f) := by
  obtain ⟨s,hs,hsval⟩ := actual_test_representative F ζ hζ U R P H μG hμG hR realization f
  apply Lp.ext
  have ht := A.T_formula i (KPContActualSectorTestEmbeddings.iota f) s hs
  have hg := (KPCubeAverage.smooth_memLp (A.chart i).n (A.chart i).a
      (actualLocalCoefficient F ζ hζ U R P H K hK A i f)
      (actualLocalCoefficient_smooth F ζ hζ U R P H μG hμG hR realization K hK A i f)).coeFn_toLp
  filter_upwards [ht,hg] with x htx hgx
  rw [hgx, htx]
  rw [hsval]
  rfl

theorem actual_form_graph_lift (A : Localizers F ζ hζ U R P H K hK) :
    ∃ L : ∀ i : Fin A.count, Q →L[ℂ]
        KPCubeGraphRellich.GraphSpace (A.chart i).n (A.chart i).a,
      ∀ i, (KPCubeGraphRellich.projection (A.chart i).n (A.chart i).a).comp (L i) =
        (A.T i).comp (jU) := by
  obtain ⟨C,hC,hbound⟩ := actual_smooth_jet_bound F ζ hζ U R P H μG hμG hR realization K hK A
  have hext : ∀ i : Fin A.count, ∃ L : Q →L[ℂ] KPCubeGraphRellich.GraphSpace (A.chart i).n (A.chart i).a,
      (KPCubeGraphRellich.projection (A.chart i).n (A.chart i).a).comp L = (A.T i).comp (jU) := by
    intro i
    obtain ⟨L,-,-,hL⟩ := KPLocalizedFormGraph.dense_bounded_extension
      (KPContActualFormCutoffClosedProduct.graphTestLinear F ζ hζ U R P H μG hμG hR realization)
      (actual_coreTest_dense F ζ hζ U R P H μG hμG hR realization)
      (actualCoreJet F ζ hζ U R P H μG hμG hR realization K hK A i)
      (C i) (hC i) (hbound i)
      (KPCubeGraphRellich.projection (A.chart i).n (A.chart i).a)
      ((A.T i).comp (jU)) (by
        intro f
        change (KPCubeAverage.smooth_memLp (A.chart i).n (A.chart i).a
          (actualLocalCoefficient F ζ hζ U R P H K hK A i f)
          (actualLocalCoefficient_smooth F ζ hζ U R P H μG hμG hR realization K hK A i f)).toLp _ =
            A.T i (KPContActualSectorTestEmbeddings.iota f)
        exact actualCoreJet_projection_test F ζ hζ U R P H μG hμG hR realization K hK A i f)
    exact ⟨L,hL⟩
  choose L hL using hext
  exact ⟨L,hL⟩

theorem restriction_factorization (A : Localizers F ζ hζ U R P H K hK) :
    ChartFactorization F ζ hζ U R P H μG hμG hR realization K hK A := by
  obtain ⟨L, hL⟩ := actual_form_graph_lift F ζ hζ U R P H μG hμG hR realization K hK A
  refine ⟨L, hL, ?_⟩
  simp_rw [hL]
  apply ContinuousLinearMap.ext
  intro u
  have hrec := congrArg (fun T : HU →L[ℂ] H_K F ζ hζ U R P H K => T (jU u)) A.reconstruction
  simpa [r_K, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply] using hrec

theorem restriction_isCompactOperator :
    IsCompactOperator (r_K F ζ hζ U R P H μG hμG hR realization K hK) := by
  obtain ⟨A⟩ :=
    kp_cont_actual_fixed_haar_core_localizers F ζ hζ μG hμG U R hR P H realization K hK
  obtain ⟨L, _, hfactor⟩ :=
    restriction_factorization F ζ hζ U R P H μG hμG hR realization K hK A
  rw [hfactor]
  apply (compactOperator (RingHom.id ℂ) _ _).sum_mem
  intro i _
  have hJ := KPCubeGraphRellich.projection_isCompactOperator
    (A.chart i).n (A.chart i).positive_n (A.chart i).a (A.chart i).positive_a
  have hJL : IsCompactOperator
      ((KPCubeGraphRellich.projection (A.chart i).n (A.chart i).a).comp (L i)) :=
    hJ.comp_clm (L i)
  exact hJL.continuous_comp (A.Rmap i).continuous

theorem restriction_closedBall_isCompact :
    IsCompact (closure (r_K F ζ hζ U R P H μG hμG hR realization K hK ''
      Metric.closedBall (0 : Q) 1)) := by
  obtain ⟨K₀, hK₀, hsub⟩ :=
    (restriction_isCompactOperator F ζ hζ U R P H μG hμG hR realization K hK).image_closedBall_subset_compact 1
  exact hK₀.closure_of_subset hsub

def SmoothScalar (ρ : X_U F ζ hζ U → ℂ) : Prop :=
  Continuous ρ ∧ ∀ a : KPContActualSectorSmoothTestModules.ActualChart (U := U) (H := H),
    KPContActualSectorSmoothTestModules.SmoothOnLift a
      (fun x => ρ (KPContCotangentOverlapRationalBranches.q a x.val))

section BoundedMultiplier
variable (ρ : X_U F ζ hζ U → ℂ) (hρ : Continuous ρ) (B : ℝ) (hB : 0 ≤ B)
variable (hbρ : ∀ x, ‖ρ x‖ ≤ B)
 def weight (x : CoveredSpherical F ζ hζ U) : ℂ := ρ (q F ζ hζ U x)
include hρ in
private theorem weight_cont : Continuous (weight F ζ hζ U ρ) :=
  hρ.comp (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U)
include hρ B hbρ in
 theorem mulMem (f : CoveredL2 F ζ hζ R U) :
    MemLp (fun x => weight F ζ hζ U ρ x * f x) 2 (coveredMeasure F ζ hζ R U) := by
  have hm : AEStronglyMeasurable (weight F ζ hζ U ρ) (coveredMeasure F ζ hζ R U) :=
    (weight_cont F ζ hζ U ρ hρ).measurable.aestronglyMeasurable
  exact (memLp_top_of_bound hm B (Filter.Eventually.of_forall fun x => hbρ _)).mul (Lp.memLp f)
 def mulLinear : CoveredL2 F ζ hζ R U →ₗ[ℂ] CoveredL2 F ζ hζ R U where
  toFun f := (mulMem F ζ hζ U R ρ hρ B hbρ f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(mulMem F ζ hζ U R ρ hρ B hbρ (f+g)).coeFn_toLp,
      (mulMem F ζ hζ U R ρ hρ B hbρ f).coeFn_toLp, (mulMem F ζ hζ U R ρ hρ B hbρ g).coeFn_toLp,
      Lp.coeFn_add f g,
      Lp.coeFn_add ((mulMem F ζ hζ U R ρ hρ B hbρ f).toLp _) ((mulMem F ζ hζ U R ρ hρ B hbρ g).toLp _)]
      with x h1 h2 h3 h4 h5
    simp only [h1,h5,Pi.add_apply,h2,h3,h4,mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(mulMem F ζ hζ U R ρ hρ B hbρ (c • f)).coeFn_toLp,
      (mulMem F ζ hζ U R ρ hρ B hbρ f).coeFn_toLp, Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((mulMem F ζ hζ U R ρ hρ B hbρ f).toLp _)] with x h1 h2 h3 h4
    simp only [RingHom.id_apply,h1,h4,Pi.smul_apply,h2,h3,smul_eq_mul,mul_left_comm]
 def mulCLM : CoveredL2 F ζ hζ R U →L[ℂ] CoveredL2 F ζ hζ R U := by
  refine (mulLinear F ζ hζ U R ρ hρ B hbρ).mkContinuous B ?_
  intro f
  change ‖(mulMem F ζ hζ U R ρ hρ B hbρ f).toLp _‖ ≤ B * ‖f‖
  rw [Lp.norm_toLp,Lp.norm_def]
  have hh : eLpNorm (fun x => weight F ζ hζ U ρ x * f x) 2 (coveredMeasure F ζ hζ R U) ≤
      ENNReal.ofReal B * eLpNorm f 2 (coveredMeasure F ζ hζ R U) := by
    calc _ ≤ eLpNorm (fun x => (B : ℂ) * f x) 2 (coveredMeasure F ζ hζ R U) := by
           apply eLpNorm_mono (mulMem F ζ hζ U R ρ hρ B hbρ f).aestronglyMeasurable
           intro x
           rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB]
           exact mul_le_mul_of_nonneg_right (hbρ _) (norm_nonneg _)
         _ = _ := by
           change eLpNorm ((B : ℂ) • (fun x => f x)) 2 (coveredMeasure F ζ hζ R U) = _
           rw [eLpNorm_const_smul, ← ofReal_norm,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB]
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := B)) (Lp.memLp f).eLpNorm_ne_top) hh
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB] at hr
  exact hr
include hρ B hB hbρ in
private theorem mulCLM_ae (f : CoveredL2 F ζ hζ R U) :
    mulCLM F ζ hζ U R ρ hρ B hB hbρ f =ᵐ[coveredMeasure F ζ hζ R U]
      (fun x => weight F ζ hζ U ρ x * f x) :=
  (mulMem F ζ hζ U R ρ hρ B hbρ f).coeFn_toLp
include hρ B hB hbρ in
 theorem mulCLM_mem (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) :
    mulCLM F ζ hζ U R ρ hρ B hB hbρ u.val ∈ KPContSectorClosedLpSubspace.H F ζ hζ R U := by
  rw [mem_H_iff]
  intro ε
  have ha := mulCLM_ae F ζ hζ U R ρ hρ B hB hbρ u.val
  have haz := (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε).quasiMeasurePreserving.ae ha
  have hu := (mem_H_iff F ζ hζ R U u.val).mp u.property ε
  filter_upwards [ha,haz,hu] with x h1 h2 h3
  change mulCLM F ζ hζ U R ρ hρ B hB hbρ u.val (z F ζ hζ U ε x) =
    (chi F ζ hζ ε : ℂ) * mulCLM F ζ hζ U R ρ hρ B hB hbρ u.val x
  rw [h2,h1]
  have hw : weight F ζ hζ U ρ (z F ζ hζ U ε x) = weight F ζ hζ U ρ x := by rw [weight,weight,q_z]
  change u.val (z F ζ hζ U ε x) = (chi F ζ hζ ε : ℂ) * u.val x at h3
  rw [hw,h3,mul_left_comm]
 def sectorCLM : KPContSectorClosedLpSubspace.H F ζ hζ R U →L[ℂ] KPContSectorClosedLpSubspace.H F ζ hζ R U :=
  (((mulCLM F ζ hζ U R ρ hρ B hB hbρ).comp (KPContSectorClosedLpSubspace.H F ζ hζ R U).subtypeL).codRestrict
    (KPContSectorClosedLpSubspace.H F ζ hζ R U) (mulCLM_mem F ζ hζ U R ρ hρ B hB hbρ))

private theorem scalar_mask_formula (K : Set (X_U F ζ hζ U)) (hK : MeasurableSet K)
    (s : BorelL2Sections F ζ hζ U R P H) :
    (scalarRepresentative F ζ hζ U R P H (mask F ζ hζ U R P H K hK s).val).val =
      (fun x => K.indicator (fun _ => (scalarRepresentative F ζ hζ U R P H s.val).val x)
        (q F ζ hζ U x)) := by
  let g := scalarRepresentative F ζ hζ U R P H s.val
  let gK : GenuineCoveredScalars F ζ hζ U := ⟨fun x =>
    K.indicator (fun _ => g.val x) (q F ζ hζ U x), by
      intro ε x
      change K.indicator (fun _ => g.val (z F ζ hζ U ε x)) (q F ζ hζ U (z F ζ hζ U ε x)) =
        (chi F ζ hζ ε : ℂ) * K.indicator (fun _ => g.val x) (q F ζ hζ U x)
      rw [q_z]
      by_cases hx : q F ζ hζ U x ∈ K
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        exact g.property ε x
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
        simp⟩
  have hg : S F ζ hζ U R P H g = s.val := (S F ζ hζ U R P H).apply_symm_apply s.val
  have he : S F ζ hζ U R P H gK = (mask F ζ hζ U R P H K hK s).val := by
    funext i
    apply Subtype.ext
    funext x
    rw [S_apply, mask_val_apply]
    change K.indicator (fun _ => g.val (Quotient.mk _ (x,(H.atlas U).representative i)))
      (q F ζ hζ U (Quotient.mk _ (x,(H.atlas U).representative i))) = _
    rw [q_mk]
    change K.indicator (fun _ => g.val (Quotient.mk _ (x,(H.atlas U).representative i)))
      (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i) (Quotient.mk _ x)) = _
    rw [← (H.atlas U).components_formula]
    have hxg := congrArg (fun t => (t i).val x) hg
    rw [S_apply] at hxg
    rw [hxg]
  have hback := congrArg (S F ζ hζ U R P H).symm he
  rw [LinearEquiv.symm_apply_apply] at hback
  exact congrArg (fun f : GenuineCoveredScalars F ζ hζ U => f.val) hback.symm

include hρ B hB hbρ in
theorem bounded_multiplier_exists : ∃ M : H_U F ζ hζ U R →L[ℂ] H_U F ζ hζ U R,
    ∀ u, ((M u).val : CoveredSpherical F ζ hζ U → ℂ) =ᵐ[coveredMeasure F ζ hζ R U]
      (fun x => ρ (q F ζ hζ U x) * u.val x) := by
  refine ⟨sectorCLM F ζ hζ U R ρ hρ B hB hbρ, ?_⟩
  intro u
  exact mulCLM_ae F ζ hζ U R ρ hρ B hB hbρ u.val

theorem restriction_mask_ae (K : Set (X_U F ζ hζ U)) (hK : MeasurableSet K)
    (u : H_U F ζ hζ U R) :
    (((sectorLineIsometry F ζ hζ U R P H).symm
      (zeroExtension F ζ hζ U R P H K hK (res_K F ζ hζ U R P H K hK u))).val :
        CoveredSpherical F ζ hζ U → ℂ) =ᵐ[coveredMeasure F ζ hζ R U]
      (fun x => K.indicator (fun _ => u.val x) (q F ζ hζ U x)) := by
  obtain ⟨s,hs⟩ := @Submodule.Quotient.mk_surjective ℂ (BorelL2Sections F ζ hζ U R P H)
    inferInstance inferInstance inferInstance (nullSections F ζ hζ U R P H)
      (sectorLineIsometry F ζ hζ U R P H u)
  change mk F ζ hζ U R P H s = sectorLineIsometry F ζ hζ U R P H u at hs
  have hus : (sectorLineIsometry F ζ hζ U R P H).symm (mk F ζ hζ U R P H s) = u := by
    rw [hs, LinearIsometryEquiv.symm_apply_apply]
  have hm : zeroExtension F ζ hζ U R P H K hK (res_K F ζ hζ U R P H K hK u) =
      mk F ζ hζ U R P H (mask F ζ hζ U R P H K hK s) := by
    change zeroExtension F ζ hζ U R P H K hK
      (lineRestriction F ζ hζ U R P H K hK (sectorLineIsometry F ζ hζ U R P H u)) = _
    rw [← hs,lineRestriction_mk]
    rfl
  rw [hm]
  have ha := (representative_memLp F ζ hζ U R P H (mask F ζ hζ U R P H K hK s)).coeFn_toLp
  have hb := (representative_memLp F ζ hζ U R P H s).coeFn_toLp
  rw [← sectorLineIsometry_symm_mk, hus] at hb
  rw [sectorLineIsometry_symm_mk]
  filter_upwards [ha,hb] with x hax hbx
  rw [hax]
  rw [congrFun (scalar_mask_formula F ζ hζ U R P H K hK s) x]
  by_cases hx : q F ζ hζ U x ∈ K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hbx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
end BoundedMultiplier

variable (ρ : X_U F ζ hζ U → ℂ)

structure MultiplierData where
  M_ρ : HU →L[ℂ] HU
  m_ρ_K : H_K F ζ hζ U R P H (tsupport ρ) →L[ℂ] HU
  global_formula : ∀ u : HU,
    ((M_ρ u).val : KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ U → ℂ)
      =ᵐ[KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U]
        (fun x => ρ (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x) * u.val x)
  localized_formula : ∀ v : H_K F ζ hζ U R P H (tsupport ρ),
    ((m_ρ_K v).val : KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ U → ℂ)
      =ᵐ[KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U]
        (fun x => ρ (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x) *
          (((sectorLineIsometry F ζ hζ U R P H).symm
            (zeroExtension F ζ hζ U R P H (tsupport ρ)
              (isClosed_tsupport ρ).measurableSet v)).val x))
  multiplication_factor : M_ρ = m_ρ_K.comp
    (res_K F ζ hζ U R P H (tsupport ρ) (isClosed_tsupport ρ).measurableSet)

  resolvent_factor : ∀ hρ : HasCompactSupport ρ,
    M_ρ.comp BU = m_ρ_K.comp
      ((r_K F ζ hζ U R P H μG hμG hR realization (tsupport ρ) hρ).comp
        (b_U F ζ hζ U R P H μG hμG hR realization))
  localized_compact : IsCompactOperator (M_ρ.comp BU)

theorem multiplierData_nonempty (hρ : SmoothScalar F ζ hζ U R P H ρ)
    (hcρ : HasCompactSupport ρ) :
    Nonempty (MultiplierData F ζ hζ U R P H μG hμG hR realization ρ) := by
  have hbdd : BddAbove (Set.range (fun x : X_U F ζ hζ U => ‖ρ x‖)) :=
    hρ.1.norm.bddAbove_range_of_hasCompactSupport hcρ.norm
  let B : ℝ := max 1 (sSup (Set.range (fun x : X_U F ζ hζ U => ‖ρ x‖)))
  have hB : 0 ≤ B := le_trans zero_le_one (le_max_left _ _)
  have hbρ : ∀ x : X_U F ζ hζ U, ‖ρ x‖ ≤ B := fun x =>
    le_trans (le_csSup hbdd ⟨x, rfl⟩) (le_max_right _ _)
  obtain ⟨M, hM⟩ := bounded_multiplier_exists F ζ hζ U R ρ hρ.1 B hB hbρ
  let ext : H_K F ζ hζ U R P H (tsupport ρ) →L[ℂ] HU :=
    LinearMap.mkContinuous
      (((sectorLineIsometry F ζ hζ U R P H).symm.toLinearEquiv.toLinearMap).comp
        (zeroExtension F ζ hζ U R P H (tsupport ρ) (isClosed_tsupport ρ).measurableSet))
      1 (fun v => by
        rw [LinearMap.comp_apply, one_mul]
        change ‖(sectorLineIsometry F ζ hζ U R P H).symm
          ((zeroExtension F ζ hζ U R P H (tsupport ρ) (isClosed_tsupport ρ).measurableSet) v)‖ ≤ ‖v‖
        rw [LinearIsometryEquiv.norm_map, zeroExtension_norm])
  let m : H_K F ζ hζ U R P H (tsupport ρ) →L[ℂ] HU := M.comp ext
  have hext_apply : ∀ v : H_K F ζ hζ U R P H (tsupport ρ),
      ext v = (sectorLineIsometry F ζ hζ U R P H).symm
        (zeroExtension F ζ hζ U R P H (tsupport ρ) (isClosed_tsupport ρ).measurableSet v) :=
    fun _ => rfl
  have hglob : ∀ u : HU, ((M u).val : CoveredSpherical F ζ hζ U → ℂ)
      =ᵐ[coveredMeasure F ζ hζ R U] (fun x => ρ (q F ζ hζ U x) * u.val x) := fun u => hM u
  have hloc : ∀ v : H_K F ζ hζ U R P H (tsupport ρ),
      ((m v).val : CoveredSpherical F ζ hζ U → ℂ)
      =ᵐ[coveredMeasure F ζ hζ R U]
        (fun x => ρ (q F ζ hζ U x) *
          (((sectorLineIsometry F ζ hζ U R P H).symm
            (zeroExtension F ζ hζ U R P H (tsupport ρ)
              (isClosed_tsupport ρ).measurableSet v)).val x)) := by
    intro v
    have h := hM (ext v)
    rw [hext_apply v] at h
    change ((M (ext v)).val : CoveredSpherical F ζ hζ U → ℂ)
      =ᵐ[coveredMeasure F ζ hζ R U]
        (fun x => ρ (q F ζ hζ U x) *
          (((sectorLineIsometry F ζ hζ U R P H).symm
            (zeroExtension F ζ hζ U R P H (tsupport ρ)
              (isClosed_tsupport ρ).measurableSet v)).val x))
    exact h
  have hmul : M = m.comp
      (res_K F ζ hζ U R P H (tsupport ρ) (isClosed_tsupport ρ).measurableSet) := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    rw [Lp.ext_iff]
    have h1 := hM u
    have h2 := hM (ext (res_K F ζ hζ U R P H (tsupport ρ)
      (isClosed_tsupport ρ).measurableSet u))
    have h3 := restriction_mask_ae F ζ hζ U R P H (tsupport ρ)
      (isClosed_tsupport ρ).measurableSet u
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [hext_apply] at hx2
    show (M u).val x = (M (ext (res_K F ζ hζ U R P H (tsupport ρ)
      (isClosed_tsupport ρ).measurableSet u))).val x
    rw [hext_apply]
    rw [hx1, hx2, hx3]
    by_cases hx : q F ζ hζ U x ∈ tsupport ρ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, mul_zero, image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hres : ∀ hc : HasCompactSupport ρ, M.comp BU = m.comp
      ((r_K F ζ hζ U R P H μG hμG hR realization (tsupport ρ) hc).comp
        (b_U F ζ hζ U R P H μG hμG hR realization)) := by
    intro hc
    rw [hmul, r_K]
    have hresK : res_K F ζ hζ U R P H (tsupport ρ) hc.measurableSet =
        res_K F ζ hζ U R P H (tsupport ρ) (isClosed_tsupport ρ).measurableSet :=
      congrArg (fun pr => res_K F ζ hζ U R P H (tsupport ρ) pr)
        (Subsingleton.elim hc.measurableSet (isClosed_tsupport ρ).measurableSet)
    rw [hresK]
    simp only [ContinuousLinearMap.comp_assoc,
      (b_U_properties F ζ hζ U R P H μG hμG hR realization).1]
  refine ⟨⟨M, m, hglob, hloc, hmul, hres, ?_⟩⟩
  rw [hres hcρ]
  exact ((restriction_isCompactOperator F ζ hζ U R P H μG hμG hR realization
    (tsupport ρ) hcρ).comp_clm (b_U F ζ hζ U R P H μG hμG hR realization)).continuous_comp
      m.continuous

structure Properties : Prop where
  form_norm : ∀ v : Q, ‖v‖ ^ 2 = qU v + ‖jU v‖ ^ 2
  form_lift : (jU).comp (b_U F ζ hζ U R P H μG hμG hR realization) = BU ∧
    ‖b_U F ζ hζ U R P H μG hμG hR realization‖ ≤ 1
  finite_factorization : ∀ (K : Set (X_U F ζ hζ U)) (hK : IsCompact K)
      (A : Localizers F ζ hζ U R P H K hK),
    ChartFactorization F ζ hζ U R P H μG hμG hR realization K hK A
  compact_restriction : ∀ (K : Set (X_U F ζ hζ U)) (hK : IsCompact K),
    IsCompactOperator (r_K F ζ hζ U R P H μG hμG hR realization K hK)
  compact_unit_ball : ∀ (K : Set (X_U F ζ hζ U)) (hK : IsCompact K),
    IsCompact (closure (r_K F ζ hζ U R P H μG hμG hR realization K hK ''
      Metric.closedBall (0 : Q) 1))
  localized_resolvent : ∀ ρ : X_U F ζ hζ U → ℂ,
    SmoothScalar F ζ hζ U R P H ρ → HasCompactSupport ρ →
      Nonempty (MultiplierData F ζ hζ U R P H μG hμG hR realization ρ)

end

end DedekindZetaZeroFree.KPContActualFormLocalRestrictionCompact

namespace DedekindZetaZeroFree

theorem kp_cont_actual_form_local_restriction_compact
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualFormLocalRestrictionCompact.Properties F ζ hζ U R P H μG hμG hR realization := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun v => KPContActualFormLocalRestrictionCompact.form_norm_sq F ζ hζ U R P H μG hμG hR realization v
  · exact KPContActualFormLocalRestrictionCompact.b_U_properties F ζ hζ U R P H μG hμG hR realization
  · exact fun K hK A => KPContActualFormLocalRestrictionCompact.restriction_factorization F ζ hζ U R P H μG hμG hR realization K hK A
  · exact fun K hK => KPContActualFormLocalRestrictionCompact.restriction_isCompactOperator F ζ hζ U R P H μG hμG hR realization K hK
  · exact fun K hK => KPContActualFormLocalRestrictionCompact.restriction_closedBall_isCompact F ζ hζ U R P H μG hμG hR realization K hK
  · exact fun ρ hρ hcρ => KPContActualFormLocalRestrictionCompact.multiplierData_nonempty F ζ hζ U R P H μG hμG hR realization ρ hρ hcρ

end DedekindZetaZeroFree

end
