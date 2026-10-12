module

public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.ZonalApproximation
public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.RotationCalculus

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable def zonalPolynomial (N : ℕ) (p : Ambient × Ambient) : ℂ :=
  ((N + 1 : ℂ) / 2^N) * ((1 + inner ℝ p.1 p.2) : ℂ)^N

private theorem zonalPolynomial_smooth (N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (zonalPolynomial N) := by
  exact contDiff_const.mul ((contDiff_const.add (Complex.ofRealCLM.contDiff.comp
    (contDiff_fst.inner ℝ contDiff_snd))).pow N)

instance instCompactSpaceZonalRotationSphere : CompactSpace Sphere :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient) 1)

set_option maxHeartbeats 800000 in
private theorem zonal_ambient_differentiable (N : ℕ) {F : Sphere → ℂ}
    (hF : Continuous F) (x : Ambient) :
    DifferentiableAt ℝ (fun z : Ambient => ∫ y : Sphere,
      zonalPolynomial N (z, y) * F y ∂sphereArea) x := by
  letI := sphereArea_isProbabilityMeasure
  let K := zonalPolynomial N
  let D (z : Ambient) (y : Sphere) : Ambient →L[ℝ] ℂ :=
    F y • (fderiv ℝ K (z, y)).comp (ContinuousLinearMap.inl ℝ Ambient Ambient)
  have hD : Continuous (fun p : Ambient × Sphere => D p.1 p.2) := by
    exact (hF.comp continuous_snd).smul
      ((((zonalPolynomial_smooth N).continuous_fderiv (by simp)).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).clm_comp
          continuous_const)
  have hK (z : Ambient) : Continuous (fun y : Sphere => K (z, y) * F y) :=
    (((zonalPolynomial_smooth N).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)).mul hF)
  obtain ⟨C, hC⟩ := (isCompact_closedBall x 1 |>.prod (isCompact_univ : IsCompact (univ : Set Sphere))).bddAbove_image hD.norm.continuousOn
  have hb : ∀ y z, z ∈ Metric.closedBall x 1 → ‖D z y‖ ≤ C := by
    intro y z hz
    exact hC (show ‖D z y‖ ∈ (fun p : Ambient × Sphere => ‖D p.1 p.2‖) ''
      (Metric.closedBall x 1 ×ˢ (univ : Set Sphere)) from ⟨(z, y), ⟨hz, mem_univ y⟩, rfl⟩)
  have hd : ∀ (y : Sphere) (z : Ambient), HasFDerivAt (fun z => K (z, y) * F y) (D z y) z := by
    intro y z
    have hp : HasFDerivAt (fun z : Ambient => (z, (y : Ambient)))
        (ContinuousLinearMap.inl ℝ Ambient Ambient) z := by
      convert (hasFDerivAt_id z).prodMk (hasFDerivAt_const (y : Ambient) z) using 1
      · rfl
      · ext v <;> rfl
    exact (((zonalPolynomial_smooth N).differentiable (by simp)
      (z, (y : Ambient))).hasFDerivAt.comp z hp).mul_const (F y)
  have hi := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := sphereArea) (F := fun z y => K (z, y) * F y) (F' := D)
    (bound := fun _ => C) (Metric.closedBall_mem_nhds x (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall (fun z => (hK z).aestronglyMeasurable))
    ((hK x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun y z hz => hb y z hz)) (integrable_const C)
    (Filter.Eventually.of_forall (fun y z _ => hd y z))
  exact hi.differentiableAt

private theorem zonal_radial_differentiable (N : ℕ) {F : Sphere → ℂ}
    (hF : Continuous F) (x : Sphere) :
    DifferentiableAt ℝ (radialExtension (rawZonalIntegral N F)) (x : Ambient) := by
  have hn : (x : Ambient) ≠ 0 := by
    intro h
    have := x.property
    simp [Metric.mem_sphere, h] at this
  have hs : ‖(x : Ambient)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property
  have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : Ambient => ‖z‖⁻¹ • z) (x : Ambient) :=
    ((contDiffAt_norm ℝ hn).inv (norm_ne_zero_iff.mpr hn)).smul contDiffAt_id
  have hd : DifferentiableAt ℝ
      ((fun v : Ambient => ∫ y : Sphere, zonalPolynomial N (v, y) * F y ∂sphereArea) ∘
        (fun z : Ambient => ‖z‖⁻¹ • z)) (x : Ambient) := by
    exact DifferentiableAt.comp (g := fun v : Ambient => ∫ y : Sphere,
        zonalPolynomial N (v, y) * F y ∂sphereArea)
      (f := fun z : Ambient => ‖z‖⁻¹ • z) (x : Ambient)
      (zonal_ambient_differentiable N hF _) (hnorm.differentiableAt (by simp))
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hn] with z hz
  simp only [radialExtension, dif_pos hz, Function.comp_def, rawZonalIntegral,
    zonalPolynomial]

private theorem zonal_orthogonal (N : ℕ) (e : Ambient ≃ₗᵢ[ℝ] Ambient)
    (F : Sphere → ℂ) (x : Sphere) :
    rawZonalIntegral N F (sphereOrthogonal e x) =
      rawZonalIntegral N (fun y => F (sphereOrthogonal e y)) x := by
  unfold rawZonalIntegral
  rw [← (sphereOrthogonal_measurePreserving e).integral_comp
    (sphereOrthogonal e).measurableEmbedding]
  simp only [sphereOrthogonal_coe, e.inner_map_map]

private theorem zonal_flow_derivative (N : ℕ) (i : Fin 3) {F : Sphere → ℂ}
    (hF : IsSphereSmooth F) (x : Sphere) (t : ℝ) :
    HasDerivAt (fun t => rawZonalIntegral N F (sphereOrthogonal (rotationFlow i t) x))
      (rawZonalIntegral N (rotationDeriv i F) (sphereOrthogonal (rotationFlow i t) x)) t := by
  letI := sphereArea_isProbabilityMeasure
  let K : Sphere → ℂ := fun y => zonalPolynomial N ((x : Ambient), y)
  let P : ℝ → Sphere → ℂ := fun t y => K y * F (sphereOrthogonal (rotationFlow i t) y)
  let P' : ℝ → Sphere → ℂ := fun t y => K y * rotationDeriv i F (sphereOrthogonal (rotationFlow i t) y)
  have hK : Continuous K := (zonalPolynomial_smooth N).continuous.comp
    (continuous_const.prodMk continuous_subtype_val)
  have hKi : Integrable K sphereArea :=
    hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm : ∀ t, AEStronglyMeasurable (P t) sphereArea := by
    intro t
    exact hKi.aestronglyMeasurable.mul
      (hF.continuous.comp (sphereOrthogonal (rotationFlow i t)).continuous).aestronglyMeasurable
  have hm' : ∀ t, AEStronglyMeasurable (P' t) sphereArea := by
    intro t
    exact hKi.aestronglyMeasurable.mul
      ((rotationDeriv_smooth i hF).continuous.comp (sphereOrthogonal (rotationFlow i t)).continuous).aestronglyMeasurable
  have hi : Integrable (P t) sphereArea := by
    apply hKi.mul_bdd
      (hF.continuous.comp (sphereOrthogonal (rotationFlow i t)).continuous).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun y => rotationWord_norm_le_rotationSup hF [] (n := 0) (by simp) _)
  have hb : ∀ y t, ‖P' t y‖ ≤ ‖K y‖ * rotationSup 1 F := by
    intro y t
    dsimp [P']
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (rotationWord_norm_le_rotationSup hF [i] (n := 1) (by simp) _) (norm_nonneg _)
  have hd : ∀ y t, HasDerivAt (fun t => P t y) (P' t y) t := by
    intro y t
    exact (sphereOrthogonal_rotationFlow_hasDerivAt i hF y t).const_mul (K y)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sphereArea) (s := univ) (F := P) (F' := P') (bound := fun y => ‖K y‖ * rotationSup 1 F)
    (x₀ := t) Filter.univ_mem (Filter.Eventually.of_forall hm) hi (hm' t)
    (Filter.Eventually.of_forall (fun y t _ => hb y t)) (hKi.norm.mul_const _)
    (Filter.Eventually.of_forall (fun y t _ => hd y t))
  have heq (u : ℝ) : (∫ y, P u y ∂sphereArea) =
      rawZonalIntegral N F (sphereOrthogonal (rotationFlow i u) x) :=
    (zonal_orthogonal N (rotationFlow i u) F x).symm
  have heq' : (∫ y, P' t y ∂sphereArea) =
      rawZonalIntegral N (rotationDeriv i F) (sphereOrthogonal (rotationFlow i t) x) :=
    (zonal_orthogonal N (rotationFlow i t) (rotationDeriv i F) x).symm
  simpa only [heq, heq'] using h.2

private theorem zonal_rotationDeriv (N : ℕ) (i : Fin 3) {F : Sphere → ℂ}
    (hF : IsSphereSmooth F) :
    rotationDeriv i (rawZonalIntegral N F) = rawZonalIntegral N (rotationDeriv i F) := by
  funext x
  have hf : HasFDerivAt (radialExtension (rawZonalIntegral N F))
      (fderiv ℝ (radialExtension (rawZonalIntegral N F)) (x : Ambient))
      (rotationFlow i 0 (x : Ambient)) := by
    simpa only [rotationFlow_zero] using
      (zonal_radial_differentiable N hF.continuous x).hasFDerivAt
  have hd := hf.comp_hasDerivAt 0 (rotationFlow_hasDerivAt i (x : Ambient) 0)
  have he : sphereOrthogonal (rotationFlow i 0) x = x := by
    apply Subtype.ext
    exact rotationFlow_zero i x
  have hd' : HasDerivAt
      (fun t => rawZonalIntegral N F (sphereOrthogonal (rotationFlow i t) x))
      (rotationDeriv i (rawZonalIntegral N F) x) 0 := by
    simpa only [Function.comp_def, ← sphereOrthogonal_coe, radialExtension_sphere,
      he, rotationDeriv] using hd
  have hc := zonal_flow_derivative N i hF x 0
  rw [he] at hc
  exact hd'.unique hc

theorem rawZonalIntegral_rotationWord (N : ℕ) (F : Sphere → ℂ)
    (hF : IsSphereSmooth F) (w : List (Fin 3)) :
    rotationWord w (rawZonalIntegral N F) =
      rawZonalIntegral N (rotationWord w F) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [rotationWord, ih]
    exact zonal_rotationDeriv N i (rotationWord_smooth w hF)

end DedekindZetaZeroFree.ComplexFractionalInverse
