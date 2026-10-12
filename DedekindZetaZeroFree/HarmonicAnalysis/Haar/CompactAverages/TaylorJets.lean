module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Convolution.GaussChartBumps

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel.CompactJets
open MeasureTheory Set Filter Topology

 theorem hasFDerivAt_average_general
    {H E K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (s : Set H) (hs : IsOpen s)
    (f : H → K → E) (f' : H → K → H →L[ℝ] E)
    (hf : ContinuousOn f.uncurry (s ×ˢ univ))
    (hf' : ContinuousOn f'.uncurry (s ×ˢ univ))
    (hd : ∀ x ∈ s, ∀ k, HasFDerivAt (fun y => f y k) (f' x k) x)
    (x : H) (hx : x ∈ s) :
    HasFDerivAt (fun y => ∫ k, f y k ∂μ) (∫ k, f' x k ∂μ) x := by
  obtain ⟨t, ht, htn, hts⟩ := exists_compact_subset hs hx
  obtain ⟨M, hM⟩ := (ht.prod isCompact_univ).bddAbove_image
    ((hf'.mono (prod_mono hts Subset.rfl)).norm)
  have hslice (y : H) (hy : y ∈ s) : Continuous (f y) := by
    rw [← continuousOn_univ]
    exact hf.comp (show ContinuousOn (fun k : K => (y, k)) univ from
      (continuous_const.prodMk continuous_id).continuousOn) (by intro k hk; exact ⟨hy, hk⟩)
  have hslice' : Continuous (f' x) := by
    rw [← continuousOn_univ]
    exact hf'.comp (show ContinuousOn (fun k : K => (x, k)) univ from
      (continuous_const.prodMk continuous_id).continuousOn) (by intro k hk; exact ⟨hx, hk⟩)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := f) (F' := f') (bound := fun _ => M) (mem_interior_iff_mem_nhds.mp htn)
  · filter_upwards [hs.mem_nhds hx] with y hy
    exact ((hslice y hy).stronglyMeasurable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).aestronglyMeasurable
  · exact (hslice x hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (hslice'.stronglyMeasurable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).aestronglyMeasurable
  · filter_upwards with k
    intro y hy
    exact hM (mem_image_of_mem _ (show (y, k) ∈ t ×ˢ univ from ⟨hy, mem_univ k⟩))
  · exact integrable_const M
  · filter_upwards with k
    intro y hy
    exact hd y (hts hy) k

set_option backward.isDefEq.respectTransparency false in

theorem contDiffOn_average_of_taylor
    {H E K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (s : Set H) (hs : IsOpen s) (f : H → K → E)
    (p : H → K → FormalMultilinearSeries ℝ H E)
    (hp : ∀ k, HasFTaylorSeriesUpToOn (⊤ : ℕ∞) (fun x => f x k) (fun x => p x k) s)
    (hc : ∀ m, ContinuousOn (fun q : H × K => p q.1 q.2 m) (s ×ˢ univ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ∫ k, f x k ∂μ) s := by
  let q : H → FormalMultilinearSeries ℝ H E := fun x m => ∫ k, p x k m ∂μ
  apply HasFTaylorSeriesUpToOn.contDiffOn (f' := q)
  constructor
  · intro x hx
    have hc0 : Continuous (fun k => p x k 0) := by
      rw [← continuousOn_univ]
      exact (hc 0).comp (show ContinuousOn (fun k : K => (x, k)) univ from
        (continuous_const.prodMk continuous_id).continuousOn) (by intro k hk; exact ⟨hx, hk⟩)
    have hi := hc0.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
    change (∫ k, p x k 0 ∂μ) 0 = _
    rw [ContinuousMultilinearMap.integral_apply hi]
    apply integral_congr_ae
    filter_upwards with k
    exact (hp k).zero_eq x hx
  · intro m hm x hx
    letI : NormedAddCommGroup (H [×m]→L[ℝ] E) := ContinuousMultilinearMap.normedAddCommGroup
    letI : NormedAddCommGroup (H [×m+1]→L[ℝ] E) := ContinuousMultilinearMap.normedAddCommGroup
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => H) E
    have hd : ∀ y ∈ s, ∀ k, HasFDerivAt (fun z => p z k m)
        (p y k (m + 1)).curryLeft y := by
      intro y hy k
      exact ((hp k).fderivWithin m hm y hy).hasFDerivAt (hs.mem_nhds hy)
    have hc' : ContinuousOn (fun z : H × K => (p z.1 z.2 (m + 1)).curryLeft)
        (s ×ˢ univ) := L.continuous.comp_continuousOn (hc (m + 1))
    have h := hasFDerivAt_average_general μ s hs (fun y k => p y k m)
      (fun y k => (p y k (m + 1)).curryLeft) (hc m) hc' hd x hx
    have he : (∫ k, (p x k (m + 1)).curryLeft ∂μ) =
        (∫ k, p x k (m + 1) ∂μ).curryLeft := by
      have hcp : Continuous (fun k => p x k (m + 1)) := by
        rw [← continuousOn_univ]
        exact (hc (m + 1)).comp (show ContinuousOn (fun k : K => (x, k)) univ from
          (continuous_const.prodMk continuous_id).continuousOn)
          (by intro k hk; exact ⟨hx, hk⟩)
      have hi := hcp.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
      let L' : (H [×m+1]→L[ℝ] E) ≃L[ℝ] (H →L[ℝ] H [×m]→L[ℝ] E) :=
        L.toContinuousLinearEquiv
      exact ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ)
        (E := H [×m+1]→L[ℝ] E) (F := H →L[ℝ] H [×m]→L[ℝ] E)
        L' (φ := fun k => p x k (m + 1))
    rw [he] at h
    exact h.hasFDerivWithinAt
  · intro m _
    exact continuousOn_integral_of_compact_support isCompact_univ (hc m) (by simp)

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel.CompactJets

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel
open MeasureTheory Set Filter Topology
open scoped NumberField Classical Topology Matrix.Norms.Elementwise

theorem joint_spatial_jets_on
    {P E V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (W : Set (P × E)) (hW : IsOpen W) (f : P × E → V)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f W) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : P × E => iteratedFDeriv ℝ n (fun x => f (p.1, x)) p.2) W := by
  induction n with
  | zero =>
    simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E V).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn hf
  | succ n ih =>
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    have hi : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q : P × E => iteratedFDeriv ℝ n (fun x => f (q.1, x)) q.2) p :=
      ih.contDiffAt (hW.mem_nhds hp)
    have hd : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : P × E =>
        fderiv ℝ (iteratedFDeriv ℝ n (fun x => f (q.1, x))) q.2) p := by
      exact (hi.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)).fderiv
        contDiffAt_snd (by simp)
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    convert (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) V).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp p hd using 1
    rfl

open _root_.DedekindZetaZeroFree.PGLComplex renaming target_mk → target_mk

variable (F : Type) [Field F] [NumberField F]

abbrev Mat := NumberField.InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ

def matrixClass (M : Mat F) : L F := fun w =>
  Matrix.ProjGenLinGroup.mk (if h : (M w).det ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero (M w) h else 1)

def matrixDomain : Set (Mat F) := {M | ∀ w, (M w).det ≠ 0}

theorem matrixDomain_open : IsOpen (matrixDomain F) := by
  have he : matrixDomain F = ⋂ w, {M : Mat F | (M w).det ≠ 0} := by
    ext M
    simp [matrixDomain]
  rw [he]
  apply isOpen_iInter_of_finite
  intro w
  exact isOpen_ne_fun ((continuous_apply w).matrix_det) continuous_const

open scoped Matrix.Norms.Operator in
private theorem matrixClass_continuousAt (M : Mat F) (hM : M ∈ matrixDomain F) :
    ContinuousAt (matrixClass F) M := by
  apply continuousAt_pi.mpr
  intro w
  apply (QuotientGroup.continuous_mk).continuousAt.comp
  apply (Units.isOpenEmbedding_val (R := Matrix (Fin 2) (Fin 2) ℂ)).isEmbedding.isInducing.continuousAt_iff.mpr
  apply ContinuousAt.congr_of_eventuallyEq (continuous_apply w).continuousAt
  filter_upwards [(matrixDomain_open F).mem_nhds hM] with N hN
  simp [matrixClass, hN w, Matrix.GeneralLinearGroup.mkOfDetNeZero, Function.comp_def]

 def translatedMatrix (p : (Mat F × Mat F) × Y F) : Mat F := fun w =>
  p.1.1 w * PGLComplex.affineMatrix (p.2 w) * p.1.2 w

private theorem translatedMatrix_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (translatedMatrix F) := by
  apply contDiff_pi.mpr
  intro w
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  have hc (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Mat F × Mat F) × Y F => PGLComplex.affineMatrix (p.2 w) i j) :=
    ((contDiff_pi.mp (contDiff_pi.mp PGLComplex.contDiff_affineMatrix i) j).comp
      ((contDiff_apply ℝ _ w).comp contDiff_snd))
  simp only [translatedMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  fun_prop (disch := exact hc _ _)

private theorem translatedMatrix_class (l r : Mat F) (hl : l ∈ matrixDomain F)
    (hr : r ∈ matrixDomain F) (x : Y F) (hx : x ∈ affineDomain F) :
    matrixClass F (translatedMatrix F ((l,r),x)) =
      matrixClass F l * affineEll F x * matrixClass F r := by
  change (∀ w, (l w).det ≠ 0) at hl
  change (∀ w, (r w).det ≠ 0) at hr
  change (∀ w, PGLComplex.delta (x w) ≠ 0) at hx
  funext w
  have hd : (translatedMatrix F ((l,r),x) w).det ≠ 0 := by
    simp only [translatedMatrix, Matrix.det_mul, PGLComplex.affineMatrix_det]
    exact mul_ne_zero (mul_ne_zero (hl w) (hx w)) (hr w)
  simp only [Pi.mul_apply, matrixClass, dif_pos (hl w), dif_pos (hr w), dif_pos hd,
    affineEll, PGLComplex.affinePoint, dif_pos (hx w)]
  rw [← map_mul, ← map_mul]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

 def matrixCoordinates (M : Mat F) : Y F := fun w => PGLComplex.matrixRatios (M w)

private theorem matrixCoordinates_smoothAt (M : Mat F) (hM : ∀ w, M w 0 0 ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (matrixCoordinates F) M := by
  apply contDiffAt_pi.mpr
  intro w
  exact (PGLComplex.contDiffAt_matrixRatios (M w) (hM w)).comp M
    (contDiff_apply ℝ _ w).contDiffAt

private theorem matrixCoordinates_eq (M : Mat F) (hM : M ∈ matrixDomain F) :
    matrixCoordinates F M = fun w => PGLComplex.affineInverse (matrixClass F M w) := by
  funext w
  simp only [matrixCoordinates, matrixClass, dif_pos (hM w)]
  exact (PGLComplex.matrixRatios_mk (Matrix.GeneralLinearGroup.mkOfDetNeZero (M w) (hM w))).symm

open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming affineProductChart → affineProductChart
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming affineProductChart_source → affineProductChart_source
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming affineProductChart_target → affineProductChart_target
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming affineProductChart_apply → affineProductChart_apply
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming affineProductChart_symm_apply → affineProductChart_symm_apply
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming affineDomain_open → affineDomain_open
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming gaussTarget_open → gaussTarget_open
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming affineTarget_one → affineTarget_one
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming fromAffine_contDiff → fromAffine_contDiff
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming actualSmoothBridge → actualSmoothBridge

private theorem matrixCoordinates_reconstruct (M : Mat F) (hM : M ∈ matrixDomain F)
    (ht : matrixClass F M ∈ gaussTarget F) :
    matrixCoordinates F M ∈ affineDomain F ∧
      affineEll F (matrixCoordinates F M) = matrixClass F M := by
  rw [matrixCoordinates_eq F M hM]
  have hs := (affineProductChart F).map_target (show matrixClass F M ∈
    (affineProductChart F).target by rwa [affineProductChart_target F])
  rw [affineProductChart_symm_apply F _ ht, affineProductChart_source F] at hs
  refine ⟨hs, ?_⟩
  rw [← affineProductChart_apply F _ hs, ← affineProductChart_symm_apply F _ ht]
  exact (affineProductChart F).right_inv (by rwa [affineProductChart_target F])

theorem matrixClass_out (a : L F) :
    matrixClass F (fun w => (a w).out.val) = a := by
  funext w
  simp only [matrixClass, dite_eq_left (Matrix.GeneralLinearGroup.det_ne_zero _)]
  have he : Matrix.GeneralLinearGroup.mkOfDetNeZero (a w).out.val
      (Matrix.GeneralLinearGroup.det_ne_zero (a w).out) = (a w).out := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  rw [he]
  exact Quotient.out_eq _

theorem matrixClass_mul (l r : Mat F) (hl : l ∈ matrixDomain F)
    (hr : r ∈ matrixDomain F) :
    matrixClass F (fun w => l w * r w) = matrixClass F l * matrixClass F r := by
  change (∀ w, (l w).det ≠ 0) at hl
  change (∀ w, (r w).det ≠ 0) at hr
  funext w
  simp only [Pi.mul_apply, matrixClass, Matrix.det_mul,
    dite_eq_left (mul_ne_zero (hl w) (hr w)), dite_eq_left (hl w), dite_eq_left (hr w)]
  rw [← map_mul]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem matrix_pullback_smooth {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : L F → V) (hf : AffineSmooth F f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun M => f (matrixClass F M)) (matrixDomain F) := by
  intro M hM
  apply ContDiffAt.contDiffWithinAt
  let a := matrixClass F M
  let C : Mat F := fun w => ((a⁻¹) w).out.val
  have hC : C ∈ matrixDomain F := fun w => Matrix.GeneralLinearGroup.det_ne_zero _
  let T : Mat F → Mat F := fun N w => C w * N w
  have hTs : ContDiff ℝ (⊤ : ℕ∞) T := by
    apply contDiff_pi.mpr
    intro w
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp only [T, Matrix.mul_apply, Fin.sum_univ_two]
    fun_prop
  have hTM : T M ∈ matrixDomain F := fun w => by
    change (C w * M w).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hC w) (hM w)
  have he (N : Mat F) (hN : N ∈ matrixDomain F) :
      matrixClass F (T N) = a⁻¹ * matrixClass F N := by
    rw [matrixClass_mul F C N hC hN, matrixClass_out F]
  have htarget : matrixClass F (T M) ∈ gaussTarget F := by
    rw [he M hM]
    simpa [a] using affineTarget_one F
  have hden : ∀ w, T M w 0 0 ≠ 0 := by
    intro w
    have ht := htarget w
    change (Matrix.ProjGenLinGroup.mk (if h : (T M w).det ≠ 0 then
      Matrix.GeneralLinearGroup.mkOfDetNeZero (T M w) h else 1)) ∈ PGLComplex.affineTarget at ht
    rw [dite_eq_left (hTM w)] at ht
    exact (target_mk _).mp ht
  have hcoord := (matrixCoordinates_smoothAt F (T M) hden).comp M hTs.contDiffAt
  have hre := matrixCoordinates_reconstruct F (T M) hTM htarget
  have hfs := (hf a).contDiffAt ((affineDomain_open F).mem_nhds hre.1)
  apply (hfs.comp M hcoord).congr_of_eventuallyEq
  have hcont : ContinuousAt (fun N => matrixClass F (T N)) M :=
    (matrixClass_continuousAt F (T M) hTM).comp hTs.continuous.continuousAt
  filter_upwards [(matrixDomain_open F).mem_nhds hM,
    hcont.preimage_mem_nhds ((gaussTarget_open F).mem_nhds htarget)] with N hN ht
  have hTN : T N ∈ matrixDomain F := fun w => by
    change (C w * N w).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hC w) (hN w)
  change f (matrixClass F N) = f (a * affineEll F (matrixCoordinates F (T N)))
  rw [(matrixCoordinates_reconstruct F (T N) hTN ht).2, he N hN]
  simp

private theorem translatedMatrix_mem (l r : Mat F) (hl : l ∈ matrixDomain F)
    (hr : r ∈ matrixDomain F) (x : Y F) (hx : x ∈ affineDomain F) :
    translatedMatrix F ((l,r),x) ∈ matrixDomain F := by
  intro w
  change (l w * PGLComplex.affineMatrix (x w) * r w).det ≠ 0
  rw [Matrix.det_mul, Matrix.det_mul, PGLComplex.affineMatrix_det]
  exact mul_ne_zero (mul_ne_zero (hl w) (hx w)) (hr w)

private theorem translated_spatial_jets_continuousAt {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : L F → V) (hf : AffineSmooth F f)
    (l r : Mat F) (hl : l ∈ matrixDomain F) (hr : r ∈ matrixDomain F)
    (x : Y F) (hx : x ∈ affineDomain F) (n : ℕ) :
    ContinuousAt (fun p : (Mat F × Mat F) × Y F => iteratedFDeriv ℝ n
      (fun y => f (matrixClass F p.1.1 * affineEll F y * matrixClass F p.1.2)) p.2)
      ((l,r),x) := by
  let W := (matrixDomain F ×ˢ matrixDomain F) ×ˢ affineDomain F
  have hW : IsOpen W := ((matrixDomain_open F).prod (matrixDomain_open F)).prod (affineDomain_open F)
  have hp : ((l,r),x) ∈ W := ⟨⟨hl,hr⟩,hx⟩
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Mat F × Mat F) × Y F => f (matrixClass F (translatedMatrix F p))) W :=
    (matrix_pullback_smooth F f hf).comp (translatedMatrix_smooth F).contDiffOn
      (fun p hp => translatedMatrix_mem F _ _ hp.1.1 hp.1.2 _ hp.2)
  have hsm' : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Mat F × Mat F) × Y F =>
        f (matrixClass F p.1.1 * affineEll F p.2 * matrixClass F p.1.2)) W := by
    apply hsm.congr
    intro p hp
    rw [translatedMatrix_class F _ _ hp.1.1 hp.1.2 _ hp.2]
  exact ((joint_spatial_jets_on W hW _ hsm' n).contDiffAt (hW.mem_nhds hp)).continuousAt

def localMatrixLift (a b : L F) : Mat F := fun w =>
  (a w).out.val * PGLComplex.affineMatrix ((affineProductChart F).symm (a⁻¹ * b) w)

theorem localMatrixLift_continuousAt (a : L F) :
    ContinuousAt (localMatrixLift F a) a := by
  have h1 : (1 : L F) ∈ (affineProductChart F).target := by
    rw [affineProductChart_target F]
    exact affineTarget_one F
  have hi : ContinuousAt (fun b : L F => (affineProductChart F).symm (a⁻¹ * b)) a := by
    exact ((affineProductChart F).symm.continuousAt h1).comp_of_eq
      (continuous_const.mul continuous_id).continuousAt (by simp)
  apply continuousAt_pi.mpr
  intro w
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  have hm : ContinuousAt (fun b : L F =>
      PGLComplex.affineMatrix ((affineProductChart F).symm (a⁻¹ * b) w)) a :=
    PGLComplex.contDiff_affineMatrix.continuous.continuousAt.comp
      ((continuous_apply w).continuousAt.comp hi)
  simp only [localMatrixLift, Matrix.mul_apply, Fin.sum_univ_two]
  exact (continuousAt_const.mul ((continuous_apply j).continuousAt.comp
    ((continuous_apply 0).continuousAt.comp hm))).add
    (continuousAt_const.mul ((continuous_apply j).continuousAt.comp
      ((continuous_apply 1).continuousAt.comp hm)))

theorem localMatrixLift_reconstruct (a b : L F)
    (hb : a⁻¹ * b ∈ gaussTarget F) :
    localMatrixLift F a b ∈ matrixDomain F ∧
      matrixClass F (localMatrixLift F a b) = b := by
  let y := (affineProductChart F).symm (a⁻¹ * b)
  have hy : y ∈ affineDomain F := by
    rw [← affineProductChart_source F]
    apply (affineProductChart F).map_target
    rwa [affineProductChart_target F]
  have he : affineEll F y = a⁻¹ * b := by
    rw [← affineProductChart_apply F y hy]
    exact (affineProductChart F).right_inv (by rwa [affineProductChart_target F])
  have hC : (fun w => (a w).out.val) ∈ matrixDomain F := fun w =>
    Matrix.GeneralLinearGroup.det_ne_zero _
  have hA : (fun w => PGLComplex.affineMatrix (y w)) ∈ matrixDomain F := fun w => by
    rw [PGLComplex.affineMatrix_det]
    exact hy w
  have hM : localMatrixLift F a b ∈ matrixDomain F := fun w => by
    change ((a w).out.val * PGLComplex.affineMatrix (y w)).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hC w) (hA w)
  refine ⟨hM, ?_⟩
  rw [show localMatrixLift F a b = fun w => (a w).out.val *
      PGLComplex.affineMatrix (y w) from rfl, matrixClass_mul F _ _ hC hA, matrixClass_out F]
  have hh : matrixClass F (fun w => PGLComplex.affineMatrix (y w)) = affineEll F y := by
    funext w
    have hd : (PGLComplex.affineMatrix (y w)).det ≠ 0 := hA w
    simp only [matrixClass, dite_eq_left hd, affineEll, PGLComplex.affinePoint,
      dite_eq_left (show PGLComplex.delta (y w) ≠ 0 from hy w)]
  rw [hh, he]
  simp

theorem localMatrixLift_eventually (a : L F) :
    ∀ᶠ b in 𝓝 a, localMatrixLift F a b ∈ matrixDomain F ∧
      matrixClass F (localMatrixLift F a b) = b := by
  have hc : ContinuousAt (fun b : L F => a⁻¹ * b) a := by fun_prop
  have hn := hc.preimage_mem_nhds ((gaussTarget_open F).mem_nhds
    (show a⁻¹ * a ∈ gaussTarget F by simpa using affineTarget_one F))
  filter_upwards [hn] with b hb
  exact localMatrixLift_reconstruct F a b hb

private theorem compact_parameter_spatial_jets
    {K V : Type*} [TopologicalSpace K]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : L F → V) (hf : AffineSmooth F f)
    (l r : K → L F) (hl : Continuous l) (hr : Continuous r) (n : ℕ) :
    ContinuousOn (fun p : Y F × K => iteratedFDeriv ℝ n
      (fun y => f (l p.2 * affineEll F y * r p.2)) p.1)
      (affineDomain F ×ˢ univ) := by
  intro p hp
  let ML := localMatrixLift F (l p.2)
  let MR := localMatrixLift F (r p.2)
  have hL := localMatrixLift_reconstruct F (l p.2) (l p.2)
    (show (l p.2)⁻¹ * l p.2 ∈ gaussTarget F by simpa using affineTarget_one F)
  have hR := localMatrixLift_reconstruct F (r p.2) (r p.2)
    (show (r p.2)⁻¹ * r p.2 ∈ gaussTarget F by simpa using affineTarget_one F)
  have hML : ContinuousAt (fun q : Y F × K => ML (l q.2)) p :=
    (localMatrixLift_continuousAt F (l p.2)).comp_of_eq (hl.comp continuous_snd).continuousAt rfl
  have hMR : ContinuousAt (fun q : Y F × K => MR (r q.2)) p :=
    (localMatrixLift_continuousAt F (r p.2)).comp_of_eq (hr.comp continuous_snd).continuousAt rfl
  have hc := (translated_spatial_jets_continuousAt F f hf _ _ hL.1 hR.1 _ hp.1 n).comp_of_eq
    ((hML.prodMk hMR).prodMk continuousAt_fst) rfl
  have heL : ∀ᶠ q : Y F × K in 𝓝 p, ML (l q.2) ∈ matrixDomain F ∧
      matrixClass F (ML (l q.2)) = l q.2 :=
    (hl.comp continuous_snd).continuousAt (localMatrixLift_eventually F (l p.2))
  have heR : ∀ᶠ q : Y F × K in 𝓝 p, MR (r q.2) ∈ matrixDomain F ∧
      matrixClass F (MR (r q.2)) = r q.2 :=
    (hr.comp continuous_snd).continuousAt (localMatrixLift_eventually F (r p.2))
  have hEq : (fun q : Y F × K => iteratedFDeriv ℝ n
      (fun y => f (l q.2 * affineEll F y * r q.2)) q.1) =ᶠ[𝓝 p]
      (fun q => iteratedFDeriv ℝ n (fun y => f
        (matrixClass F (ML (l q.2)) * affineEll F y * matrixClass F (MR (r q.2)))) q.1) := by
    filter_upwards [heL, heR] with q hqL hqR
    rw [hqL.2, hqR.2]
  exact (hc.congr_of_eventuallyEq hEq).continuousWithinAt

private theorem compact_parameter_slice_smooth
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : L F → V) (hf : AffineSmooth F f) (l r : L F) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (l * affineEll F x * r)) (affineDomain F) := by
  let ML : Mat F := fun w => (l w).out.val
  let MR : Mat F := fun w => (r w).out.val
  have hL : ML ∈ matrixDomain F := fun w => Matrix.GeneralLinearGroup.det_ne_zero _
  have hR : MR ∈ matrixDomain F := fun w => Matrix.GeneralLinearGroup.det_ne_zero _
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x : Y F => translatedMatrix F ((ML,MR),x)) :=
    (translatedMatrix_smooth F).comp (contDiff_const.prodMk contDiff_id)
  have H := (matrix_pullback_smooth F f hf).comp hc.contDiffOn
    (fun x hx => translatedMatrix_mem F ML MR hL hR x hx)
  apply H.congr
  intro x hx
  change f (l * affineEll F x * r) = f (matrixClass F (translatedMatrix F ((ML,MR),x)))
  rw [translatedMatrix_class F ML MR hL hR x hx, matrixClass_out F, matrixClass_out F]

theorem averaged_kernel_smooth
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]
    (π : K → L F) (hπ : Continuous π)
    (f : L F → ℝ) (hf : KernelSmooth F f) :
    KernelSmooth F (fun a => ∫ k, f ((π k)⁻¹ * a * π k) ∂μ) := by
  apply (actualSmoothBridge F _).mpr
  intro a
  let h : Y F → K → ℝ := fun x k => f ((π k)⁻¹ * (a * affineEll F x) * π k)
  have haf := (actualSmoothBridge F f).mp hf
  have hs (k : K) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => h x k) (affineDomain F) := by
    simpa only [h, mul_assoc] using compact_parameter_slice_smooth F f haf ((π k)⁻¹ * a) (π k)
  apply CompactJets.contDiffOn_average_of_taylor μ (affineDomain F) (affineDomain_open F) h
    (fun x k => ftaylorSeriesWithin ℝ (fun x => h x k) (affineDomain F) x)
  · intro k
    exact (hs k).ftaylorSeriesWithin (affineDomain_open F).uniqueDiffOn
  · intro n
    have hj := compact_parameter_spatial_jets F f haf
      (fun k => (π k)⁻¹ * a) π (hπ.inv.mul continuous_const) hπ n
    apply hj.congr
    intro p hp
    change iteratedFDerivWithin ℝ n (fun x => h x p.2) (affineDomain F) p.1 = _
    rw [iteratedFDerivWithin_of_isOpen n (affineDomain_open F) hp.1]
    simp only [h, mul_assoc]

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel

end

end
