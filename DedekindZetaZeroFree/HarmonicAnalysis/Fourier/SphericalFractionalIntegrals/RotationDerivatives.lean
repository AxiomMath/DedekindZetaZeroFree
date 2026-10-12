module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.SphericalFractionalIntegrals.Smoothness
public import Mathlib.Data.Set.Finite.List

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.RotationCalculus
open MeasureTheory Set
open scoped RealInnerProductSpace Pointwise

noncomputable def rawRotationVector (i : Fin 3) (x : Ambient) : Ambient :=
  WithLp.toLp 2 (fun j : Fin 3 =>
    if j = i + 1 then -x (i + 2) else if j = i + 2 then x (i + 1) else 0)

noncomputable def rawRotationDeriv (i : Fin 3) (F : Sphere → ℂ) (x : Sphere) : ℂ :=
  fderiv ℝ (rawRadialExtension F) (x : Ambient) (rawRotationVector i x)

private theorem rawSphere_norm (x : Sphere) : ‖(x : Ambient)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property

private theorem rawSphere_ne_zero (x : Sphere) : (x : Ambient) ≠ 0 := by
  intro h
  have := rawSphere_norm x
  simp [h] at this

theorem rawRadialExtension_sphere (F : Sphere → ℂ) (x : Sphere) :
    rawRadialExtension F x = F x := by
  simp only [rawRadialExtension, dif_pos (rawSphere_ne_zero x), rawSphere_norm, inv_one, one_smul]

private theorem rawPuncture_open : IsOpen {x : Ambient | x ≠ 0} := isOpen_ne

private theorem rawNormalize_smooth :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Ambient => ‖x‖⁻¹ • x) {x | x ≠ 0} := by
  intro x hx
  exact (((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id).contDiffWithinAt

private theorem restrict_raw_smooth (G : Ambient → ℂ)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G {x | x ≠ 0}) :
    RawSphereSmooth (fun x : Sphere => G x) := by
  have h := hG.comp rawNormalize_smooth (fun x hx => by
    exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hx)) hx)
  apply h.congr
  intro x hx
  simp only [rawRadialExtension, dif_pos (show x ≠ 0 from hx), Function.comp_apply]

private theorem rawRotationVector_smooth (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (rawRotationVector i) := by
  unfold rawRotationVector
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro j
  simp only [rawRotationVector]
  split_ifs
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i + 2)).contDiff.neg
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i + 1)).contDiff
  · exact contDiff_const

private theorem rawRotationDeriv_smooth (i : Fin 3) {F : Sphere → ℂ} (hF : RawSphereSmooth F) :
    RawSphereSmooth (rawRotationDeriv i F) := by
  unfold rawRotationDeriv
  apply restrict_raw_smooth
    (fun x : Ambient => fderiv ℝ (rawRadialExtension F) x (rawRotationVector i x))
  exact (hF.fderiv_of_isOpen rawPuncture_open (by simp)).clm_apply
    (rawRotationVector_smooth i).contDiffOn

theorem RawSphereSmooth.continuous {F : Sphere → ℂ} (hF : RawSphereSmooth F) :
    Continuous F := by
  have h : Continuous (fun x : Sphere => rawRadialExtension F x) :=
    hF.continuousOn.comp_continuous continuous_subtype_val (fun x => rawSphere_ne_zero x)
  simpa only [rawRadialExtension_sphere] using h

noncomputable def rawSphereOrthogonal (e : Ambient ≃ₗᵢ[ℝ] Ambient) : Sphere ≃ₜ Sphere :=
  e.toHomeomorph.subtype (fun x => by
    change ‖x - 0‖ = 1 ↔ ‖e x - 0‖ = 1
    simp only [sub_zero, e.norm_map])

@[simp] theorem rawSphereOrthogonal_coe (e : Ambient ≃ₗᵢ[ℝ] Ambient) (x : Sphere) :
    (rawSphereOrthogonal e x : Ambient) = e x := rfl

theorem rawSphereOrthogonal_measurePreserving (e : Ambient ≃ₗᵢ[ℝ] Ambient) :
    MeasurePreserving (rawSphereOrthogonal e) sphereArea sphereArea := by
  have hraw : MeasurePreserving (rawSphereOrthogonal e) volume.toSphere volume.toSphere := by
    refine ⟨(rawSphereOrthogonal e).measurable, Measure.ext fun s hs => ?_⟩
    rw [(rawSphereOrthogonal e).measurableEmbedding.map_apply,
      Measure.toSphere_apply' _ ((rawSphereOrthogonal e).measurable hs),
      Measure.toSphere_apply' _ hs]
    congr 1
    have hset : Ioo (0 : ℝ) 1 • (Subtype.val '' ((rawSphereOrthogonal e) ⁻¹' s)) =
        e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
      ext z
      constructor
      · rintro ⟨t, ht, _, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨t, ht, e y, ⟨rawSphereOrthogonal e y, hy, rfl⟩, by simp⟩
      · rintro ⟨t, ht, _, ⟨y, hy, rfl⟩, heq⟩
        refine ⟨t, ht, e.symm y, ⟨(rawSphereOrthogonal e).symm y, ?_, rfl⟩, ?_⟩
        · simpa using hy
        · have := congrArg e.symm heq
          simpa using this
    rw [hset]
    exact e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding _
  exact hraw.smul_measure _

theorem fractionalKernel_rawSphereOrthogonal (α : ℝ) (e : Ambient ≃ₗᵢ[ℝ] Ambient)
    (x y : Sphere) :
    fractionalKernel α (rawSphereOrthogonal e x) (rawSphereOrthogonal e y) =
      fractionalKernel α x y := by
  simp only [fractionalKernel, rawSphereOrthogonal_coe, e.inner_map_map]

theorem fractionalIntegral_rawSphereOrthogonal (α : ℝ) (e : Ambient ≃ₗᵢ[ℝ] Ambient)
    (F : Sphere → ℂ) (x : Sphere) :
    fractionalIntegral α F (rawSphereOrthogonal e x) =
      fractionalIntegral α (fun y => F (rawSphereOrthogonal e y)) x := by
  unfold fractionalIntegral
  rw [← (rawSphereOrthogonal_measurePreserving e).integral_comp
    (rawSphereOrthogonal e).measurableEmbedding]
  simp only [fractionalKernel_rawSphereOrthogonal]

noncomputable def rawRotationFlowMap (i : Fin 3) (t : ℝ) : Ambient →ₗ[ℝ] Ambient where
  toFun x := WithLp.toLp 2 (fun j : Fin 3 =>
    if j = i then x i else if j = i + 1 then
      Real.cos t * x (i+1) - Real.sin t * x (i+2)
    else Real.sin t * x (i+1) + Real.cos t * x (i+2))
  map_add' x y := by
    ext j; simp only [PiLp.toLp_apply, PiLp.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext j; simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem rawRotationFlowMap_inverse (i : Fin 3) (t : ℝ) (x : Ambient) :
    rawRotationFlowMap i (-t) (rawRotationFlowMap i t x) = x := by
  have ht := Real.cos_sq_add_sin_sq t
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [rawRotationFlowMap, Fin.reduceAdd, Real.sin_neg, Real.cos_neg] <;>
    nlinarith [congrArg (fun a : ℝ => a * x 0) ht,
      congrArg (fun a : ℝ => a * x 1) ht,
      congrArg (fun a : ℝ => a * x 2) ht]

theorem rawRotationFlowMap_norm (i : Fin 3) (t : ℝ) (x : Ambient) :
    ‖rawRotationFlowMap i t x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have ht := Real.cos_sq_add_sin_sq t
  fin_cases i <;> simp only [Fin.sum_univ_three, rawRotationFlowMap, LinearMap.coe_mk,
    AddHom.coe_mk, PiLp.toLp_apply, Fin.reduceAdd, Real.norm_eq_abs, sq_abs] <;>
    simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

noncomputable def rawRotationFlow (i : Fin 3) (t : ℝ) : Ambient ≃ₗᵢ[ℝ] Ambient where
  toLinearEquiv :=
    { rawRotationFlowMap i t with
      invFun := rawRotationFlowMap i (-t)
      left_inv := rawRotationFlowMap_inverse i t
      right_inv := fun x => by
        change rawRotationFlowMap i t (rawRotationFlowMap i (-t) x) = x
        simpa only [neg_neg] using rawRotationFlowMap_inverse i (-t) x }
  norm_map' := rawRotationFlowMap_norm i t

@[simp] theorem rawRotationFlow_apply (i : Fin 3) (t : ℝ) (x : Ambient) :
    rawRotationFlow i t x = rawRotationFlowMap i t x := rfl

@[simp] theorem rawRotationFlow_zero (i : Fin 3) (x : Ambient) : rawRotationFlow i 0 x = x := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [rawRotationFlowMap, rawRotationFlow, Fin.reduceAdd]

theorem rawRotationFlow_hasDerivAt (i : Fin 3) (x : Ambient) (t : ℝ) :
    HasDerivAt (fun t => rawRotationFlow i t x) (rawRotationVector i (rawRotationFlow i t x)) t := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hp : HasDerivAt (fun t => (rawRotationFlow i t x).ofLp)
      ((rawRotationVector i (rawRotationFlow i t x)).ofLp) t := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [rawRotationFlow_apply, rawRotationFlowMap, rawRotationVector, Fin.reduceAdd]
    all_goals
      first
      | exact hasDerivAt_const t _
      | convert ((Real.hasDerivAt_cos t).mul_const _).sub
          ((Real.hasDerivAt_sin t).mul_const _) using 1 <;> ring
      | convert ((Real.hasDerivAt_sin t).mul_const _).add
          ((Real.hasDerivAt_cos t).mul_const _) using 1 <;> ring
  exact e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hp

theorem rawSphereOrthogonal_rawRotationFlow_hasDerivAt (i : Fin 3) {F : Sphere → ℂ}
    (hF : RawSphereSmooth F) (x : Sphere) (t : ℝ) :
    HasDerivAt (fun t => F (rawSphereOrthogonal (rawRotationFlow i t) x))
      (rawRotationDeriv i F (rawSphereOrthogonal (rawRotationFlow i t) x)) t := by
  have hn : (rawSphereOrthogonal (rawRotationFlow i t) x : Ambient) ≠ 0 := by
    intro hz
    have hs := (rawSphereOrthogonal (rawRotationFlow i t) x).property
    simp [Metric.mem_sphere, hz] at hs
  have hd := ((hF _ hn).contDiffAt (isOpen_ne.mem_nhds hn)).differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp_hasDerivAt t (rawRotationFlow_hasDerivAt i (x : Ambient) t)
  simpa only [Function.comp_def, ← rawSphereOrthogonal_coe, rawRadialExtension_sphere,
    rawRotationDeriv] using hc

theorem fractionalIntegral_rawRotationFlow_hasDerivAt (α : ℝ) (hα : 0 < α) (i : Fin 3)
    {F : Sphere → ℂ} (hF : RawSphereSmooth F) (x : Sphere) (t : ℝ) :
    HasDerivAt (fun t => fractionalIntegral α F (rawSphereOrthogonal (rawRotationFlow i t) x))
      (fractionalIntegral α (rawRotationDeriv i F)
        (rawSphereOrthogonal (rawRotationFlow i t) x)) t := by
  let K : Sphere → ℂ := fun y => fractionalKernel α x y
  let P : ℝ → Sphere → ℂ := fun t y => K y * F (rawSphereOrthogonal (rawRotationFlow i t) y)
  let P' : ℝ → Sphere → ℂ :=
    fun t y => K y * rawRotationDeriv i F (rawSphereOrthogonal (rawRotationFlow i t) y)
  have hK := (fractionalKernel_mass α hα).2 x
  have hKi : Integrable K sphereArea := hK.1.ofReal
  letI : CompactSpace Sphere :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient) 1)
  obtain ⟨C0, hC0⟩ : ∃ C : ℝ, ∀ y : Sphere, ‖F y‖ ≤ C := by
    have hbdd : BddAbove ((fun y : Sphere => ‖F y‖) '' Set.univ) :=
      isCompact_univ.bddAbove_image hF.continuous.norm.continuousOn
    exact ⟨_, fun y => le_csSup hbdd ⟨y, Set.mem_univ y, rfl⟩⟩
  obtain ⟨C1, hC1⟩ : ∃ C : ℝ, ∀ y : Sphere, ‖rawRotationDeriv i F y‖ ≤ C := by
    have hbdd : BddAbove ((fun y : Sphere => ‖rawRotationDeriv i F y‖) '' Set.univ) :=
      isCompact_univ.bddAbove_image (rawRotationDeriv_smooth i hF).continuous.norm.continuousOn
    exact ⟨_, fun y => le_csSup hbdd ⟨y, Set.mem_univ y, rfl⟩⟩
  have hmeas : ∀ t, AEStronglyMeasurable (P t) sphereArea := by
    intro t
    exact hKi.aestronglyMeasurable.mul
      (hF.continuous.comp (rawSphereOrthogonal (rawRotationFlow i t)).continuous).aestronglyMeasurable
  have hmeas' : ∀ t, AEStronglyMeasurable (P' t) sphereArea := by
    intro t
    exact hKi.aestronglyMeasurable.mul
      ((rawRotationDeriv_smooth i hF).continuous.comp
        (rawSphereOrthogonal (rawRotationFlow i t)).continuous).aestronglyMeasurable
  have hPi : Integrable (P t) sphereArea := by
    apply hKi.mul_bdd
      (hF.continuous.comp (rawSphereOrthogonal (rawRotationFlow i t)).continuous).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun y => by
      simpa only [Function.comp_apply] using
        hC0 (rawSphereOrthogonal (rawRotationFlow i t) y))
  have hb : ∀ y t, ‖P' t y‖ ≤ fractionalKernel α x y * C1 := by
    intro y t
    dsimp only [P', K]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK.2.1 y)]
    exact mul_le_mul_of_nonneg_left (hC1 _) (hK.2.1 y)
  have hder : ∀ y t, HasDerivAt (fun t => P t y) (P' t y) t := by
    intro y t
    exact (rawSphereOrthogonal_rawRotationFlow_hasDerivAt i hF y t).const_mul (K y)
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sphereArea) (s := univ) (F := P) (F' := P')
    (bound := fun y => fractionalKernel α x y * C1)
    (x₀ := t) (Filter.univ_mem) (Filter.Eventually.of_forall hmeas) hPi (hmeas' t)
    (Filter.Eventually.of_forall (fun y x _ => hb y x)) (hK.1.mul_const _)
    (Filter.Eventually.of_forall (fun y x _ => hder y x))
  have heq (u : ℝ) : (∫ y, P u y ∂sphereArea) =
      fractionalIntegral α F (rawSphereOrthogonal (rawRotationFlow i u) x) :=
    (fractionalIntegral_rawSphereOrthogonal α (rawRotationFlow i u) F x).symm
  have heq' : (∫ y, P' t y ∂sphereArea) =
      fractionalIntegral α (rawRotationDeriv i F)
        (rawSphereOrthogonal (rawRotationFlow i t) x) :=
    (fractionalIntegral_rawSphereOrthogonal α (rawRotationFlow i t)
      (rawRotationDeriv i F) x).symm
  simpa only [heq, heq'] using hi.2

theorem fractionalIntegral_raw_rotationDeriv (α : ℝ) (hα : 0 < α)
    (i : Fin 3) (F : Sphere → ℂ) (hF : RawSphereSmooth F) :
    rawRotationDeriv i (fractionalIntegral α F) =
      fractionalIntegral α (rawRotationDeriv i F) := by
  funext x
  have hsm : RawSphereSmooth (fractionalIntegral α F) :=
    fractionalIntegral_raw_smooth α hα F hF
  have hdiff : DifferentiableAt ℝ (rawRadialExtension (fractionalIntegral α F)) (x : Ambient) :=
    ((hsm x (rawSphere_ne_zero x)).contDiffAt
      (rawPuncture_open.mem_nhds (rawSphere_ne_zero x))).differentiableAt (by simp)
  have hf : HasFDerivAt (rawRadialExtension (fractionalIntegral α F))
      (fderiv ℝ (rawRadialExtension (fractionalIntegral α F)) (x : Ambient))
      (rawRotationFlow i 0 (x : Ambient)) := by
    simpa only [rawRotationFlow_zero] using hdiff.hasFDerivAt
  have hd := hf.comp_hasDerivAt 0 (rawRotationFlow_hasDerivAt i (x : Ambient) 0)
  have he : rawSphereOrthogonal (rawRotationFlow i 0) x = x := by
    apply Subtype.ext
    exact rawRotationFlow_zero i x
  have hd' : HasDerivAt
      (fun t => fractionalIntegral α F (rawSphereOrthogonal (rawRotationFlow i t) x))
      (rawRotationDeriv i (fractionalIntegral α F) x) 0 := by
    simpa only [Function.comp_def, ← rawSphereOrthogonal_coe, rawRadialExtension_sphere,
      he, rawRotationFlow_zero, rawRotationDeriv] using hd
  have hc := fractionalIntegral_rawRotationFlow_hasDerivAt α hα i hF x 0
  rw [he] at hc
  exact hd'.unique hc

end DedekindZetaZeroFree.ComplexFractionalInverse.RotationCalculus
