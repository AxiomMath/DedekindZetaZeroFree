module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.HaarLocalizers.LineRestriction
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.SphericalChartModulus

@[expose] public section

set_option maxHeartbeats 2400000
noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPFixedHaarLocalizersBodies

open KPContActualFixedHaarCoreLocalizers KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

attribute [local instance 5000] KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line
attribute [local instance 5000] KPContSectorLineL2Isometry.instNormedSpaceL2Line
attribute [local instance 5000] KPContSectorLineL2Isometry.instInnerProductSpaceL2Line

 abbrev instTopologicalSpaceL2LineLocal : TopologicalSpace (L2Line F ζ hζ U R P H) :=
  (KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line F ζ hζ U R P H).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceL2LineLocal

 abbrev instAddCommMonoidL2LineLocal : AddCommMonoid (L2Line F ζ hζ U R P H) :=
  (KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line F ζ hζ U R P H).toSeminormedAddCommGroup.toAddCommMonoid

attribute [local instance 5000] instAddCommMonoidL2LineLocal

 abbrev instTopologicalSpaceHULocal : TopologicalSpace (H_U F ζ hζ U R) :=
  (inferInstance : NormedAddCommGroup (H_U F ζ hζ U R)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceHULocal

 abbrev instTopologicalSpaceHKLocal (K : Set (X_U F ζ hζ U)) :
    TopologicalSpace (H_K F ζ hζ U R P H K) :=
  (inferInstance : NormedAddCommGroup (H_K F ζ hζ U R P H K)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceHKLocal

 abbrev instAddCommMonoidHKLocal (K : Set (X_U F ζ hζ U)) :
    AddCommMonoid (H_K F ζ hζ U R P H K) :=
  (inferInstance : NormedAddCommGroup (H_K F ζ hζ U R P H K)).toSeminormedAddCommGroup.toAddCommMonoid

attribute [local instance 5000] instAddCommMonoidHKLocal

open scoped InnerProductSpace Matrix
open HyperbolicChart
 def scaleTFun (d : ℕ) (z : KPArch.Space d) (v : KPArch.Space d) :
    HyperbolicChart.Space d :=
  WithLp.toLp 2 (fun ik : Fin d × Fin 3 =>
    if ik.2 = 2 then (v ik.1).2
    else (KPArch.height (z ik.1))⁻¹ *
      (if ik.2 = 0 then (v ik.1).1.re else (v ik.1).1.im))

 def scaleTLin (d : ℕ) (z : KPArch.Space d) :
    KPArch.Space d →ₗ[ℝ] HyperbolicChart.Space d where
  toFun := scaleTFun d z
  map_add' := by
    intro a b
    ext ik
    simp only [scaleTFun, PiLp.toLp_apply, Pi.add_apply, Prod.fst_add, Prod.snd_add,
      Complex.add_re, Complex.add_im]
    by_cases h2 : ik.2 = 2
    · simp [h2]
    · by_cases h0 : ik.2 = 0
      · simp [h2, h0, mul_add]
      · simp [h2, h0, mul_add]
  map_smul' := by
    intro c a
    ext ik
    simp only [scaleTFun, PiLp.toLp_apply, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd,
      Complex.smul_re, Complex.smul_im]
    by_cases h2 : ik.2 = 2
    · simp [h2]
    · by_cases h0 : ik.2 = 0
      · simp [h2, h0, mul_comm, mul_left_comm, mul_assoc]
      · simp [h2, h0, mul_comm, mul_left_comm, mul_assoc]

 def scaleT (d : ℕ) (z : KPArch.Space d) :
    KPArch.Space d →L[ℝ] HyperbolicChart.Space d :=
  (scaleTLin d z).toContinuousLinearMap

private lemma scaleT_apply (d : ℕ) (z : KPArch.Space d) (v : KPArch.Space d) :
    scaleT d z v = scaleTFun d z v := rfl

private lemma scaleT_norm_sq (d : ℕ) (z : KPArch.Space d) (v : KPArch.Space d) :
    ‖scaleT d z v‖ ^ 2 = KPArch.metric d z v := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, KPArch.metric]
  simp only [scaleT_apply, scaleTFun, PiLp.toLp_apply, Fin.sum_univ_three]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  norm_num
  ring

private lemma gram_quadform {n d : ℕ}
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] HyperbolicChart.Space d)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    (∑ j, ∑ k, ((‖S (EuclideanSpace.single j 1 + EuclideanSpace.single k 1)‖ ^ 2 -
        ‖S (EuclideanSpace.single j 1)‖ ^ 2 - ‖S (EuclideanSpace.single k 1)‖ ^ 2) / 2)
        * ξ j * ξ k) = ‖S ξ‖ ^ 2 := by
  have hinner : ∀ j k, ((‖S (EuclideanSpace.single j 1 + EuclideanSpace.single k 1)‖ ^ 2 -
        ‖S (EuclideanSpace.single j 1)‖ ^ 2 - ‖S (EuclideanSpace.single k 1)‖ ^ 2) / 2)
        = ⟪S (EuclideanSpace.single j 1), S (EuclideanSpace.single k 1)⟫_ℝ := by
    intro j k
    rw [map_add, norm_add_sq_real]
    ring
  simp only [hinner]
  have hξ : ξ = ∑ j, ξ j • EuclideanSpace.single j 1 := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr ξ]
    simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
  have hS : S ξ = ∑ j, ξ j • S (EuclideanSpace.single j 1) := by
    conv_lhs => rw [hξ]
    rw [map_sum]
    simp only [map_smul]
  rw [hS, ← real_inner_self_eq_norm_sq]
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

private theorem metric_positive (C : Chart F ζ hζ U R P H) :
    ∀ x ∈ C.extendedDomain, (C.metricMatrix F ζ hζ H.totallyComplex U x).PosDef := by
  let d := KPCuspLogShape.dimension F
  have hscale : ∀ z : KPArch.Space d, Function.Injective (scaleT d z) := by
    intro z v w h
    have heq : ∀ i k, scaleTFun d z v (i, k) = scaleTFun d z w (i, k) :=
      fun i k => congrArg (fun a : HyperbolicChart.Space d => a (i, k)) h
    ext i : 1
    apply Prod.ext
    · apply Complex.ext
      · have hh := heq i 0
        simpa [scaleTFun, KPArch.height, Real.exp_ne_zero] using hh
      · have hh := heq i 1
        simpa [scaleTFun, KPArch.height, Real.exp_ne_zero] using hh
    · have hh := heq i 2
      simpa [scaleTFun] using hh
  have hinj : ∀ x ∈ C.extendedDomain, Function.Injective (fderiv ℝ C.coordinates x) := by
    obtain ⟨g, hg, hleft⟩ := C.smooth_inverse
    intro x hx
    have hc := (C.smooth_coordinates.contDiffAt (C.open_extendedDomain.mem_nhds hx)).differentiableAt (by simp)
    have hg' := (hg.contDiffAt (C.coordinates_open.mem_nhds ⟨x, hx, rfl⟩)).differentiableAt (by simp)
    have heq : (g ∘ C.coordinates) =ᶠ[𝓝 x] id := by
      filter_upwards [C.open_extendedDomain.mem_nhds hx] with y hy
      exact hleft y hy
    have hder : (fderiv ℝ g (C.coordinates x)).comp (fderiv ℝ C.coordinates x) =
        ContinuousLinearMap.id ℝ (KPCoreChartLocalizers.E C.n) := by
      rw [← fderiv_comp x hg' hc, heq.fderiv_eq]
      exact fderiv_id
    intro v w hvw
    have := congrArg (fun T : KPCoreChartLocalizers.E C.n →L[ℝ] KPCoreChartLocalizers.E C.n => T v) hder
    have := congrArg (fun T : KPCoreChartLocalizers.E C.n →L[ℝ] KPCoreChartLocalizers.E C.n => T w) hder
    have hv : fderiv ℝ g (C.coordinates x) (fderiv ℝ C.coordinates x v) = v :=
      congrArg (fun T : KPCoreChartLocalizers.E C.n →L[ℝ] KPCoreChartLocalizers.E C.n => T v) hder
    have hw : fderiv ℝ g (C.coordinates x) (fderiv ℝ C.coordinates x w) = w :=
      congrArg (fun T : KPCoreChartLocalizers.E C.n →L[ℝ] KPCoreChartLocalizers.E C.n => T w) hder
    rw [hvw, hw] at hv
    exact hv.symm
  let Sx : KPCoreChartLocalizers.E C.n → (KPCoreChartLocalizers.E C.n →L[ℝ] HyperbolicChart.Space d) :=
    fun x => (scaleT d (C.coordinates x)).comp (fderiv ℝ C.coordinates x)
  have hmetric : ∀ x w, KPArch.metric d (C.coordinates x) (fderiv ℝ C.coordinates x w) = ‖Sx x w‖ ^ 2 := by
    intro x w
    exact (scaleT_norm_sq d _ _).symm
  dsimp only [d] at hmetric
  have hMentry : ∀ x j k, C.metricMatrix F ζ hζ H.totallyComplex U x j k =
      ⟪Sx x (EuclideanSpace.single j 1), Sx x (EuclideanSpace.single k 1)⟫_ℝ := by
    intro x j k
    unfold KPCoreChartLocalizers.Chart.metricMatrix
    rw [hmetric, hmetric, hmetric, map_add, norm_add_sq_real]
    ring
  have hquad : ∀ x (v : Fin C.n → ℝ),
      v ⬝ᵥ (C.metricMatrix F ζ hζ H.totallyComplex U x *ᵥ v) = ‖Sx x (WithLp.toLp 2 v)‖ ^ 2 := by
    intro x v
    rw [← gram_quadform (Sx x) (WithLp.toLp 2 v)]
    simp only [KPCoreChartLocalizers.Chart.metricMatrix, hmetric, dotProduct, Matrix.mulVec, Finset.mul_sum,
      PiLp.toLp_apply]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hposdef : ∀ x ∈ C.extendedDomain, (C.metricMatrix F ζ hζ H.totallyComplex U x).PosDef := by
    intro x hx
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    constructor
    · ext j k
      simp only [Matrix.conjTranspose_apply, star_trivial, hMentry]
      exact real_inner_comm _ _
    · intro v hv
      simp only [star_trivial, hquad]
      apply sq_pos_of_pos
      apply norm_pos_iff.mpr
      intro heq
      have hh : Sx x (WithLp.toLp 2 v) = Sx x 0 := by simpa using heq
      have hz := hinj x hx ((hscale (C.coordinates x)) hh)
      apply hv
      exact congrArg WithLp.ofLp hz
  exact hposdef

theorem metric_upper_bound (C : Chart F ζ hζ U R P H) : ∃ B : ℝ,
    ∀ x ∈ closure (Metric.ball (0 : KPCoreChartLocalizers.E C.n) C.radius),
    ∀ ξ : KPCoreChartLocalizers.E C.n,
      (∑ j, ∑ k, C.energyMatrix F ζ hζ H.totallyComplex U x j k * ξ j * ξ k) ≤ B * ‖ξ‖ ^ 2 := by
  have hc : ContinuousOn (C.metricMatrix F ζ hζ H.totallyComplex U) C.extendedDomain := by
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro k
    have hD := C.smooth_coordinates.continuousOn_fderiv_of_isOpen C.open_extendedDomain (by simp)
    have hf (v : KPCoreChartLocalizers.E C.n) : ContinuousOn (fun x => fderiv ℝ C.coordinates x v) C.extendedDomain :=
      hD.clm_apply continuousOn_const
    have hm (v : KPCoreChartLocalizers.E C.n) : ContinuousOn
        (fun x => KPArch.metric (KPCuspLogShape.dimension F) (C.coordinates x) (fderiv ℝ C.coordinates x v)) C.extendedDomain := by
      unfold KPArch.metric KPArch.height
      apply continuousOn_finset_sum
      intro i hi
      have hci := ((continuous_apply i).comp_continuousOn C.smooth_coordinates.continuousOn).snd
      have hfi := (continuous_apply i).comp_continuousOn (hf v)
      convert ((hfi.fst.norm.div (Real.continuous_exp.comp_continuousOn hci) (fun x hx => Real.exp_ne_zero _)).pow 2).add (hfi.snd.pow 2) using 1 <;> funext x <;> simp [Function.comp_def, div_pow, div_eq_mul_inv, mul_comm, mul_pow, inv_pow]
    exact (((hm _).sub (hm _)).sub (hm _)).div_const 2
  have he : ContinuousOn (C.energyMatrix F ζ hζ H.totallyComplex U) C.extendedDomain := by
    intro x hx
    have hu := (Matrix.isUnit_iff_isUnit_det _).mp (metric_positive F ζ hζ U R P H C x hx).isUnit
    exact (continuousAt_matrix_inv _ (hu.unit_spec ▸ NormedRing.inverse_continuousAt hu.unit)).comp_continuousWithinAt (hc x hx)
  let K := closure (Metric.ball (0 : KPCoreChartLocalizers.E C.n) C.radius)
  have hK : IsCompact K := by
    rw [show K = Metric.closedBall (0 : KPCoreChartLocalizers.E C.n) C.radius from closure_ball _ C.positive_radius.ne']
    exact isCompact_closedBall _ _
  have hentry : ∀ j k : Fin C.n, ∃ B : ℝ, ∀ x ∈ K,
      |C.energyMatrix F ζ hζ H.totallyComplex U x j k| ≤ B := by
    intro j k
    have hc' := (continuous_apply k).comp_continuousOn
      ((continuous_apply j).comp_continuousOn (he.mono C.closed_ball_in_extension))
    obtain ⟨B,hB0,hB⟩ := (hK.image_of_continuousOn hc'.abs).bddAbove.exists_ge 0
    exact ⟨B,fun x hx => hB _ ⟨x,hx,rfl⟩⟩
  choose B hB using hentry
  let B' := ∑ j : Fin C.n, ∑ k : Fin C.n, max (B j k) 0
  have hB' : ∀ j k : Fin C.n, max (B j k) 0 ≤ B' := by
    intro j k
    exact (Finset.single_le_sum (fun i hi => le_max_right _ _) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (fun i hi => Finset.sum_nonneg (fun l hl => le_max_right _ _)) (Finset.mem_univ j))
  have hB'0 : 0 ≤ B' := Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => le_max_right _ _
  refine ⟨(C.n:ℝ)^2 * B',?_⟩
  intro x hx ξ
  calc
    _ ≤ ∑ j : Fin C.n, ∑ k : Fin C.n, B' * ‖ξ‖^2 := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      have hentry : |C.energyMatrix F ζ hζ H.totallyComplex U x j k| ≤ B' :=
        (hB j k x hx).trans ((le_max_left _ _).trans (hB' j k))
      have hj' : |ξ j| ≤ ‖ξ‖ := PiLp.norm_apply_le ξ j
      have hk' : |ξ k| ≤ ‖ξ‖ := PiLp.norm_apply_le ξ k
      calc
        _ ≤ |C.energyMatrix F ζ hζ H.totallyComplex U x j k| * |ξ j| * |ξ k| := by
          rw [← abs_mul,← abs_mul]; exact le_abs_self _
        _ ≤ B' * ‖ξ‖ * ‖ξ‖ := mul_le_mul (mul_le_mul hentry hj' (abs_nonneg _) (by positivity)) hk'
          (abs_nonneg _) (by positivity)
        _ = _ := by ring
    _ = _ := by simp [Finset.sum_const, Fintype.card_fin]; ring

theorem componentWeight_toReal_pos (i : Fin (H.atlas U).componentCount) :
    0 < ((H.disintegration U).componentWeight i).toReal :=
  ENNReal.toReal_pos (ne_of_gt ((H.disintegration U).positive_componentWeight i))
    (ne_of_lt ((H.disintegration U).finite_componentWeight i))

theorem actualWeight_bounds (C : Chart F ζ hζ U R P H) :
    0 < ((H.disintegration U).componentWeight C.component).toReal * C.lower ∧
    ∀ x ∈ closure (Metric.ball (0 : KPCoreChartLocalizers.E C.n) C.radius),
      ((H.disintegration U).componentWeight C.component).toReal * C.lower ≤
        actualWeight F ζ hζ U R P H C x ∧
      actualWeight F ζ hζ U R P H C x ≤
        ((H.disintegration U).componentWeight C.component).toReal * C.upper := by
  have hc := componentWeight_toReal_pos F ζ hζ U R P H C.component
  refine ⟨mul_pos hc C.positive_lower, ?_⟩
  intro x hx
  exact ⟨mul_le_mul_of_nonneg_left (C.finite_bounds x hx).1 hc.le,
    mul_le_mul_of_nonneg_left (C.finite_bounds x hx).2 hc.le⟩

theorem smooth_cutoff_coefficient
    (C : Chart F ζ hζ U R P H) (η : KPCoreChartLocalizers.E C.n → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Metric.ball 0 C.radius)
    (s : Sections F ζ hζ U R P H) (hs : IsSmoothSections F ζ hζ U R P H s) :
    let g := fun x => (η x : ℂ) * (s C.component).val (C.coordinates x)
    ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      tsupport g ⊆ interior (KPCoreChartLocalizers.cube C.n C.a) := by
  dsimp only
  let g := fun x => (η x : ℂ) * (s C.component).val (C.coordinates x)
  have hcut : ContDiff ℝ (⊤ : ℕ∞) (fun x => (η x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hη
  have hsupport : tsupport g ⊆ tsupport η :=
    Set.Subset.trans tsupport_mul_subset_left (by
      apply tsupport_comp_subset (g := fun x : ℝ => (x : ℂ))
      rfl)
  refine ⟨?_, hηc.of_isClosed_subset (isClosed_tsupport g) hsupport,
    hsupport.trans (hηs.trans (subset_closure.trans C.closed_ball_in_cube))⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport η
  · have hxe : x ∈ C.extendedDomain := C.closed_ball_in_extension
      (subset_closure (hηs hx))
    exact hcut.contDiffAt.mul ((hs C.component).contDiffAt.comp x
      (C.smooth_coordinates.contDiffAt (C.open_extendedDomain.mem_nhds hxe)))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [g, hy]

theorem average_cutoff_section
    (C : Chart F ζ hζ U R P H) (η : KPCoreChartLocalizers.E C.n → ℝ)
    (hη : ∀ (g : C.G F ζ hζ H.totallyComplex U) x, η (C.orthogonal g x) = η x)
    (s : Sections F ζ hζ U R P H) {x : KPCoreChartLocalizers.E C.n}
    (hx : x ∈ Metric.ball 0 C.radius) :
    ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
      (C.average F ζ hζ H.totallyComplex U
        (fun y => (η y : ℂ) * (s C.component).val (C.coordinates y)) x) : ℂ) =
      (η x : ℂ) * (s C.component).val (C.coordinates x) := by
  have heq : ∀ (g : C.G F ζ hζ H.totallyComplex U) y,
      y ∈ Metric.ball 0 C.radius →
      (η (C.orthogonal g y) : ℂ) * (s C.component).val (C.coordinates (C.orthogonal g y)) =
        (C.rho F ζ hζ H.totallyComplex U g : ℂ) *
          ((η y : ℂ) * (s C.component).val (C.coordinates y)) := by
    intro g y hy
    rw [hη, C.equivariance g y (C.closed_ball_in_extension (subset_closure hy))]
    have hs := (s C.component).property.2 g.val (C.coordinates y)
    rw [hs]
    simp only [KPCoreChartLocalizers.Chart.rho, MonoidHom.comp_apply, Subgroup.subtype_apply]
    ring
  rw [C.average_eq_self F ζ hζ H.totallyComplex U _ heq hx]
  let v : KPCuspGenuineMonodromy.scalarFiber F ζ hζ U :=
    ⟨(η x : ℂ) * (s C.component).val (C.coordinates x),
      (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).smul_mem (η x : ℂ)
        ((s C.component).property.1 (C.coordinates x))⟩
  exact congrArg Subtype.val
    ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto_mem_subspace_eq_self v)

 def mulSections (φ : X_U F ζ hζ U → ℝ) (s : Sections F ζ hζ U R P H) :
    Sections F ζ hζ U R P H := fun i =>
  ⟨fun x => (φ ((H.atlas U).components ⟨i, Quotient.mk _ x⟩) : ℂ) * (s i).val x,
    (by intro x; exact (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).smul_mem _ ((s i).property.1 x)),
    (by
      intro γ x
      have hq : (Quotient.mk _ ((γ : KPCuspArithmetic.PGL2 F) • x) :
          KPCuspSiegel.OrbitQuotient F (KPCuspGenuineMonodromy.Component F ζ hζ U
            ((H.atlas U).representative i))) = Quotient.mk _ x :=
        (Quotient.sound (MulAction.orbitRel_apply.mpr
          (MulAction.mem_orbit_iff.mpr ⟨γ⁻¹, inv_smul_smul γ x⟩))).symm
      dsimp only
      rw [hq, (s i).property.2 γ x]
      ring)⟩

 theorem mulSections_norm (φ : X_U F ζ hζ U → ℝ) (s : Sections F ζ hζ U R P H)
    (b : X_U F ζ hζ U) :
    sectionNorm F ζ hζ U R P H (mulSections F ζ hζ U R P H φ s) b =
      |φ b| * sectionNorm F ζ hζ U R P H s b := by
  obtain ⟨⟨i,q⟩,rfl⟩ := (H.atlas U).components.surjective b
  refine Quotient.inductionOn q fun x => ?_
  rw [sectionNorm_component, sectionNorm_component]
  exact (norm_mul _ _).trans (by rw [Complex.norm_real, Real.norm_eq_abs])

 def mulBorel (φ : X_U F ζ hζ U → ℝ)
    (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun z => φ
      (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative j)
        (KPCuspSiegel.projection F _ z))))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ b, |φ b| ≤ M)
    (s : BorelL2Sections F ζ hζ U R P H) : BorelL2Sections F ζ hζ U R P H := by
  refine ⟨mulSections F ζ hζ U R P H φ s.val, ?_, ?_⟩
  · intro i
    have hm : Measurable (fun x => φ ((H.atlas U).components ⟨i,Quotient.mk _ x⟩)) := by
      convert (hφ i).continuous.measurable using 1
      funext x
      rw [(H.atlas U).components_formula]
      rfl
    exact hm.complex_ofReal.mul (s.property.1 i)
  · unfold normIntegral squaredNorm
    have he : ∀ b, ENNReal.ofReal (sectionNorm F ζ hζ U R P H
        (mulSections F ζ hζ U R P H φ s.val) b ^ 2) ≤
        ENNReal.ofReal (M^2) * squaredNorm F ζ hζ U R P H s.val b := by
      intro b
      rw [mulSections_norm, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) (hbound b) 2)) _
    apply (lintegral_mono he).trans_lt
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top s.property.2

private theorem sectionNorm_nonneg (s : Sections F ζ hζ U R P H)
    (b : X_U F ζ hζ U) : 0 ≤ sectionNorm F ζ hζ U R P H s b := by
  dsimp [sectionNorm]
  refine Quotient.inductionOn ((H.atlas U).components.symm b).2 (fun x => ?_)
  exact norm_nonneg _

private theorem norm_difference_le (s t : Sections F ζ hζ U R P H) (b : X_U F ζ hζ U) :
    sectionNorm F ζ hζ U R P H (s - t) b ≤
      sectionNorm F ζ hζ U R P H s b + sectionNorm F ζ hζ U R P H t b := by
  dsimp [sectionNorm]
  refine Quotient.inductionOn ((H.atlas U).components.symm b).2 (fun x => ?_)
  exact norm_sub_le _ _

private theorem squaredNorm_zero_iff (s : Sections F ζ hζ U R P H) (b : X_U F ζ hζ U) :
    squaredNorm F ζ hζ U R P H s b = 0 ↔ sectionNorm F ζ hζ U R P H s b = 0 := by
  rw [squaredNorm, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    nlinarith [sectionNorm_nonneg F ζ hζ U R P H s b]
  · intro h
    simp [h]

private theorem zero_difference (s t : Sections F ζ hζ U R P H) (b : X_U F ζ hζ U)
    (hs : squaredNorm F ζ hζ U R P H s b = 0)
    (ht : squaredNorm F ζ hζ U R P H t b = 0) :
    squaredNorm F ζ hζ U R P H (s - t) b = 0 := by
  apply (squaredNorm_zero_iff F ζ hζ U R P H _ b).mpr
  have h := norm_difference_le F ζ hζ U R P H s t b
  rw [(squaredNorm_zero_iff F ζ hζ U R P H s b).mp hs,
    (squaredNorm_zero_iff F ζ hζ U R P H t b).mp ht, zero_add] at h
  exact le_antisymm h (sectionNorm_nonneg F ζ hζ U R P H _ b)

private theorem local_null_global
    (K : Set (X_U F ζ hζ U)) (hK : MeasurableSet K)
    (C : Chart F ζ hζ U R P H)
    (hchart : Measure.map (C.toBase F ζ hζ H.totallyComplex U)
      ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball 0 C.radius)).withDensity
          (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x))) =
      (muU F ζ hζ U R P).restrict (C.O F ζ hζ H.totallyComplex U))
    (s : BorelL2Sections F ζ hζ U R P H)
    (heq : ∀ᵐ x ∂volume.restrict (Metric.ball 0 C.radius),
      C.toBase F ζ hζ H.totallyComplex U x ∈ K → (s.val C.component).val (C.coordinates x) = 0)
    (hoff : ∀ᵐ b ∂(muU F ζ hζ U R P).restrict K,
      b ∉ C.O F ζ hζ H.totallyComplex U → squaredNorm F ζ hζ U R P H s.val b = 0) :
    mkK F ζ hζ U R P H K s = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change squaredNorm F ζ hζ U R P H s.val =ᵐ[(muU F ζ hζ U R P).restrict K] 0
  let ν := ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball 0 C.radius)).withDensity
          (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x)))
  have hν : ν ≪ volume.restrict (Metric.ball 0 C.radius) :=
    Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  have hcoord : ∀ᵐ x ∂ν, C.toBase F ζ hζ H.totallyComplex U x ∈ K →
      squaredNorm F ζ hζ U R P H s.val (C.toBase F ζ hζ H.totallyComplex U x) = 0 := by
    filter_upwards [hν.ae_le heq] with x hx hmem
    rw [squaredNorm, KPCoreChartLocalizers.Chart.toBase, ← (H.atlas U).components_formula,
      KPCuspSiegel.projection, sectionNorm_component, hx hmem]
    simp
  have hm := squaredNorm_measurable F ζ hζ U R P H s.val s.property.1
  have hb : AEMeasurable (C.toBase F ζ hζ H.totallyComplex U) ν :=
    ((continuousOn_iff_continuous_restrict.mpr
      (C.toBase_ball_continuous F ζ hζ H.totallyComplex U)).aemeasurable
      Metric.isOpen_ball.measurableSet).mono_ac hν
  have hon : ∀ᵐ b ∂(muU F ζ hζ U R P).restrict (C.O F ζ hζ H.totallyComplex U),
      b ∈ K → squaredNorm F ζ hζ U R P H s.val b = 0 := by
    rw [← hchart]
    have hms : MeasurableSet {b | b ∈ K → squaredNorm F ζ hζ U R P H s.val b = 0} := by
      have he : {b | b ∈ K → squaredNorm F ζ hζ U R P H s.val b = 0} =
          Kᶜ ∪ {b | squaredNorm F ζ hζ U R P H s.val b = 0} := by
        ext b; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]; tauto
      rw [he]
      exact hK.compl.union (hm (measurableSet_singleton 0))
    exact (ae_map_iff hb hms).mpr hcoord
  rw [ae_restrict_iff' (C.open_image F ζ hζ H.totallyComplex U).measurableSet] at hon
  have hk := ae_restrict_mem (μ := muU F ζ hζ U R P) hK
  filter_upwards [Filter.Eventually.filter_mono ae_restrict_le hon, hoff, hk] with b hb ho hbk
  by_cases hx : b ∈ C.O F ζ hζ H.totallyComplex U
  · exact hb hx hbk
  · exact ho hx

theorem chart_reconstruction
    (K : Set (X_U F ζ hζ U)) (hK : IsCompact K) (C : Chart F ζ hζ U R P H)
    (φ : X_U F ζ hζ U → ℝ)
    (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun z => φ
      (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative j)
        (KPCuspSiegel.projection F _ z))))
    (hφs : tsupport φ ⊆ C.O F ζ hζ H.totallyComplex U)
    (η : KPCoreChartLocalizers.E C.n → ℝ)
    (hη : η = (Metric.ball 0 C.radius).indicator (fun x => φ (C.toBase F ζ hζ H.totallyComplex U x)))
    (hηinv : ∀ (g : C.G F ζ hζ H.totallyComplex U) x, η (C.orthogonal g x) = η x)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ b, |φ b| ≤ M)
    (T : H_U F ζ hζ U R →L[ℂ] Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a)))
    (hT : ∀ u s, sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s →
      T u =ᵐ[volume.restrict (KPCoreChartLocalizers.cube C.n C.a)]
        (fun x => (η x : ℂ) * (s.val C.component).val (C.coordinates x)))
    (Rmap : Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a)) →L[ℂ] H_K F ζ hζ U R P H K)
    (hR : ∀ f, ∃ t : BorelL2Sections F ζ hζ U R P H, Rmap f = mkK F ζ hζ U R P H K t ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball 0 C.radius), C.toBase F ζ hζ H.totallyComplex U x ∈ K →
        (t.val C.component).val (C.coordinates x) =
          ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
            (C.average F ζ hζ H.totallyComplex U f x) : ℂ)) ∧
      (∀ᵐ b ∂(muU F ζ hζ U R P).restrict K, b ∉ C.O F ζ hζ H.totallyComplex U →
        squaredNorm F ζ hζ U R P H t.val b = 0))
    (hchart : Measure.map (C.toBase F ζ hζ H.totallyComplex U)
      ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball 0 C.radius)).withDensity
          (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x))) =
      (muU F ζ hζ U R P).restrict (C.O F ζ hζ H.totallyComplex U))
    (u : H_U F ζ hζ U R) (s : BorelL2Sections F ζ hζ U R P H)
    (hs : sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s) :
    Rmap (T u) = mkK F ζ hζ U R P H K (mulBorel F ζ hζ U R P H φ hφ M hM hbound s) := by
  obtain ⟨t,ht,hball,hoff⟩ := hR (T u)
  rw [ht]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply local_null_global F ζ hζ U R P H K hK.measurableSet C hchart
  · have hsub : Metric.ball (0 : KPCoreChartLocalizers.E C.n) C.radius ⊆
        KPCoreChartLocalizers.cube C.n C.a := subset_closure.trans (C.closed_ball_in_cube.trans interior_subset)
    have ha := C.average_congr_ae F ζ hζ H.totallyComplex U
      ((hT u s hs).filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
    filter_upwards [hball,ha,ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx ha hxb hmem
    change (t.val C.component).val (C.coordinates x) -
      (φ ((H.atlas U).components ⟨C.component,Quotient.mk _ (C.coordinates x)⟩) : ℂ) *
        (s.val C.component).val (C.coordinates x) = 0
    rw [hx hmem,ha,average_cutoff_section F ζ hζ U R P H C η hηinv s.val hxb]
    rw [hη,Set.indicator_of_mem hxb]
    rw [(H.atlas U).components_formula]
    simp only [KPCoreChartLocalizers.Chart.toBase, KPCuspSiegel.projection, sub_self]
  · filter_upwards [hoff] with b hb hout
    apply zero_difference F ζ hζ U R P H _ _ b (hb hout)
    change squaredNorm F ζ hζ U R P H (mulSections F ζ hζ U R P H φ s.val) b = 0
    rw [squaredNorm,mulSections_norm]
    have hz : φ b = 0 := image_eq_zero_of_notMem_tsupport (fun h => hout (hφs h))
    simp [hz]

theorem finite_reconstruction {n : ℕ}
    (K : Set (X_U F ζ hζ U)) (hK : IsCompact K)
    (C : Fin n → Chart F ζ hζ U R P H)
    (φ : Fin n → X_U F ζ hζ U → ℝ)
    (hφ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z => φ i
      (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative j)
        (KPCuspSiegel.projection F _ z))))
    (hφs : ∀ i, tsupport (φ i) ⊆ (C i).O F ζ hζ H.totallyComplex U)
    (hpart : ∀ b ∈ K, ∑ i, φ i b = 1)
    (η : ∀ i, KPCoreChartLocalizers.E (C i).n → ℝ)
    (hη : ∀ i, η i = (Metric.ball 0 (C i).radius).indicator
      (fun x => φ i ((C i).toBase F ζ hζ H.totallyComplex U x)))
    (hηinv : ∀ i (g : (C i).G F ζ hζ H.totallyComplex U) x, η i ((C i).orthogonal g x) = η i x)
    (M : Fin n → ℝ) (hM : ∀ i, 0 ≤ M i) (hbound : ∀ i b, |φ i b| ≤ M i)
    (T : ∀ i, H_U F ζ hζ U R →L[ℂ] Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube (C i).n (C i).a)))
    (hT : ∀ i u s, sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s →
      T i u =ᵐ[volume.restrict (KPCoreChartLocalizers.cube (C i).n (C i).a)]
        (fun x => (η i x : ℂ) * (s.val (C i).component).val ((C i).coordinates x)))
    (Rmap : ∀ i, Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube (C i).n (C i).a)) →L[ℂ] H_K F ζ hζ U R P H K)
    (hR : ∀ i f, ∃ t : BorelL2Sections F ζ hζ U R P H, Rmap i f = mkK F ζ hζ U R P H K t ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball 0 (C i).radius), (C i).toBase F ζ hζ H.totallyComplex U x ∈ K →
        (t.val (C i).component).val ((C i).coordinates x) =
          ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
            ((C i).average F ζ hζ H.totallyComplex U f x) : ℂ)) ∧
      (∀ᵐ b ∂(muU F ζ hζ U R P).restrict K, b ∉ (C i).O F ζ hζ H.totallyComplex U →
        squaredNorm F ζ hζ U R P H t.val b = 0))
    (hchart : ∀ i, Measure.map ((C i).toBase F ζ hζ H.totallyComplex U)
      ((Fintype.card ((C i).G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball 0 (C i).radius)).withDensity
          (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H (C i) x))) =
      (muU F ζ hζ U R P).restrict ((C i).O F ζ hζ H.totallyComplex U)) :
    res_K F ζ hζ U R P H K hK.measurableSet = ∑ i, (Rmap i).comp (T i) := by
  apply ContinuousLinearMap.ext
  intro u
  obtain ⟨s,hs⟩ := Quotient.exists_rep (sectorLineIsometry F ζ hζ U R P H u)
  change mk F ζ hζ U R P H s = sectorLineIsometry F ζ hζ U R P H u at hs
  have hr : res_K F ζ hζ U R P H K hK.measurableSet u = mkK F ζ hζ U R P H K s := by
    change lineRestriction F ζ hζ U R P H K hK.measurableSet (sectorLineIsometry F ζ hζ U R P H u) = _
    rw [← hs,lineRestriction_mk]
  rw [hr,ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.comp_apply]
  have he : ∀ i, Rmap i (T i u) = mkK F ζ hζ U R P H K
      (mulBorel F ζ hζ U R P H (φ i) (hφ i) (M i) (hM i) (hbound i) s) := fun i =>
    chart_reconstruction F ζ hζ U R P H K hK (C i) (φ i) (hφ i) (hφs i)
      (η i) (hη i) (hηinv i) (M i) (hM i) (hbound i) (T i) (hT i)
      (Rmap i) (hR i) (hchart i) u s hs.symm
  simp_rw [he]
  rw [← map_sum]
  apply (mkK_eq_iff F ζ hζ U R P H K _ _).mpr
  filter_upwards [ae_restrict_mem hK.measurableSet] with b hb
  obtain ⟨⟨j,q⟩,rfl⟩ := (H.atlas U).components.surjective b
  refine Quotient.inductionOn q (fun x => ?_) hb
  intro hx
  rw [squaredNorm,sectionNorm_component]
  have heq : (s.val j).val x = ((∑ i, (mulBorel F ζ hζ U R P H (φ i) (hφ i)
      (M i) (hM i) (hbound i) s)).val j).val x := by
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change (s.val j).val x = ∑ i, (φ i ((H.atlas U).components ⟨j,Quotient.mk _ x⟩) : ℂ) * (s.val j).val x
    rw [← Finset.sum_mul,← Complex.ofReal_sum,hpart _ hx,Complex.ofReal_one,one_mul]
  change ENNReal.ofReal (‖(s.val j).val x - _‖ ^ 2) = 0
  rw [heq,sub_self]
  simp

end DedekindZetaZeroFree.KPFixedHaarLocalizersBodies

end
