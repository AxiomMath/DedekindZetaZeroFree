module
public import Mathlib.Analysis.Calculus.Deriv.Prod

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.IntertwinerSphericalKernelTransport
public import DedekindZetaZeroFree.Algebra.ShiftedLegendrePolynomialUniqueness
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.SphereCoordinateProjection
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section

set_option maxHeartbeats 800000

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke
open MeasureTheory ComplexFractionalInverse
open scoped RealInnerProductSpace BigOperators BoundedContinuousFunction
abbrev Ambient := RawSphereProjection.rawAmbient
abbrev Sphere := RawSphereProjection.rawSphere
noncomputable abbrev sphereArea := RawSphereProjection.rawSphereArea
noncomputable abbrev sphereArea_isProbabilityMeasure := RawSphereProjection.rawSphereArea_isProbabilityMeasure
noncomputable def polynomialSphere (p : MvPolynomial (Fin 3) ℂ) (x : Sphere) : ℂ :=
  MvPolynomial.eval (fun i => ((x : Ambient) i : ℂ)) p

noncomputable def north : Ambient := EuclideanSpace.single 0 1

@[simp] theorem north_norm : ‖north‖ = 1 := by
  simp [north, PiLp.norm_single]

theorem exists_north_rotation (x : Sphere) :
    ∃ g : Ambient ≃ₗᵢ[ℝ] Ambient, g north = (x : Ambient) := by
  let g := (ℝ ∙ (north - (x : Ambient)))ᗮ.reflection
  refine ⟨g, ?_⟩
  exact Submodule.reflection_sub (by
    rw [north_norm, mem_sphere_zero_iff_norm.mp x.property])

noncomputable def latitudeAmbient (g : Ambient ≃ₗᵢ[ℝ] Ambient) (u θ : ℝ) : Ambient :=
  g (WithLp.toLp 2 ![1 - 2*u,
    Real.sqrt (4*u*(1-u)) * Real.cos θ,
    Real.sqrt (4*u*(1-u)) * Real.sin θ])

theorem latitudeAmbient_norm (g : Ambient ≃ₗᵢ[ℝ] Ambient) (u θ : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) : ‖latitudeAmbient g u θ‖ = 1 := by
  have hs : 0 ≤ 4*u*(1-u) := by nlinarith [hu.1, hu.2]
  have hsq := Real.sq_sqrt hs
  have ht := Real.cos_sq_add_sin_sq θ
  have hn : ‖latitudeAmbient g u θ‖ ^ 2 = 1 := by
    rw [latitudeAmbient, g.norm_map, EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_succ, Fin.val_zero, Matrix.cons_val_zero,
      Fin.val_succ, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    nlinarith [sq_nonneg (Real.sqrt (4*u*(1-u)))]
  nlinarith [norm_nonneg (latitudeAmbient g u θ)]

noncomputable def latitudePoint (g : Ambient ≃ₗᵢ[ℝ] Ambient) (u θ : ℝ) : Sphere :=
  if hu : u ∈ Set.Icc (0 : ℝ) 1 then
    ⟨latitudeAmbient g u θ, mem_sphere_zero_iff_norm.mpr (latitudeAmbient_norm g u θ hu)⟩
  else ⟨g north, mem_sphere_zero_iff_norm.mpr (by rw [g.norm_map, north_norm])⟩

theorem latitudePoint_val (g : Ambient ≃ₗᵢ[ℝ] Ambient) (u θ : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (latitudePoint g u θ : Ambient) = latitudeAmbient g u θ := by
  simp [latitudePoint, hu]

theorem latitudePoint_projection (x : Sphere) (g : Ambient ≃ₗᵢ[ℝ] Ambient)
    (hg : g north = (x : Ambient)) (u θ : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (1 - inner ℝ (x : Ambient) (latitudePoint g u θ : Ambient)) / 2 = u := by
  rw [latitudePoint_val g u θ hu, ← hg, latitudeAmbient, g.inner_map_map]
  simp [north, EuclideanSpace.inner_single_left]

noncomputable def angleMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Set.Icc 0 (2 * Real.pi))

instance angleMeasure_isFiniteMeasure : IsFiniteMeasure angleMeasure := by
  exact (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))).smul_finite
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr
      (mul_pos (by norm_num) Real.pi_pos))))

noncomputable def spinMap (θ : ℝ) : Ambient →ₗ[ℝ] Ambient :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap.comp
    (LinearMap.pi ![LinearMap.proj 0,
      Real.cos θ • LinearMap.proj 1 - Real.sin θ • LinearMap.proj 2,
      Real.sin θ • LinearMap.proj 1 + Real.cos θ • LinearMap.proj 2])
    |>.comp (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap

private lemma spinMap_apply (θ : ℝ) (v : Ambient) :
    spinMap θ v = WithLp.toLp 2 ![v 0, Real.cos θ * v 1 - Real.sin θ * v 2,
      Real.sin θ * v 1 + Real.cos θ * v 2] := by
  ext i
  fin_cases i <;> simp [spinMap, WithLp.linearEquiv]

lemma spinMap_norm (θ : ℝ) (v : Ambient) : ‖spinMap θ v‖ = ‖v‖ := by
  have ht := Real.cos_sq_add_sin_sq θ
  have he : ‖spinMap θ v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [spinMap_apply]
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    have h := congrArg (fun t : ℝ => t * (v 1 ^ 2 + v 2 ^ 2)) ht
    nlinarith [h]
  nlinarith [norm_nonneg (spinMap θ v), norm_nonneg v]

noncomputable def spin (θ : ℝ) : Ambient ≃ₗᵢ[ℝ] Ambient :=
  LinearIsometryEquiv.ofSurjective
    ({spinMap θ with norm_map' := spinMap_norm θ} : Ambient →ₗᵢ[ℝ] Ambient)
    ((LinearMap.injective_iff_surjective).mp
      ({spinMap θ with norm_map' := spinMap_norm θ} : Ambient →ₗᵢ[ℝ] Ambient).injective)

private lemma spin_apply (θ : ℝ) (v : Ambient) :
    spin θ v = WithLp.toLp 2 ![v 0, Real.cos θ * v 1 - Real.sin θ * v 2,
      Real.sin θ * v 1 + Real.cos θ * v 2] := spinMap_apply θ v

private lemma latitudePoint_measurable (g : Ambient ≃ₗᵢ[ℝ] Ambient) :
    Measurable (fun z : ℝ × ℝ => latitudePoint g z.1 z.2) := by
  classical
  suffices hm : Measurable (fun z : ℝ × ℝ => (latitudePoint g z.1 z.2 : Ambient)) from
    hm.subtype_mk
  change Measurable (fun z : ℝ × ℝ => (latitudePoint g z.1 z.2 : Ambient))
  have h : Measurable (fun z : ℝ × ℝ => latitudeAmbient g z.1 z.2) := by
    unfold latitudeAmbient
    fun_prop
  have he : (fun z : ℝ × ℝ => (latitudePoint g z.1 z.2 : Ambient)) =
      (Set.Icc (0 : ℝ) 1 |> fun s => (Prod.fst ⁻¹' s).piecewise
        (fun z => latitudeAmbient g z.1 z.2) (fun _ => g north)) := by
    funext z
    by_cases hz : z.1 ∈ Set.Icc (0 : ℝ) 1 <;> simp [latitudePoint, hz, Set.piecewise]
  rw [he]
  exact h.piecewise (measurableSet_Icc.preimage measurable_fst) measurable_const

private lemma latitude_spin (u θ t : ℝ) :
    RawSphereProjection.rotation (spin t) (latitudePoint (.refl ℝ Ambient) u θ) =
      latitudePoint (.refl ℝ Ambient) u (θ + t) := by
  apply Subtype.ext
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · simp only [RawSphereProjection.rotation, latitudePoint_val _ _ _ hu,
      latitudeAmbient, spin_apply]
    ext i
    fin_cases i <;> simp [Real.cos_add, Real.sin_add] <;> ring
  · simp only [RawSphereProjection.rotation, latitudePoint, dif_neg hu]
    rw [spin_apply]
    ext i
    fin_cases i <;> simp [north]

private lemma latitude_periodic (u : ℝ) :
    Function.Periodic (latitudePoint (.refl ℝ Ambient) u) (2 * Real.pi) := by
  intro θ
  apply Subtype.ext
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · simp [latitudePoint_val _ _ _ hu, latitudeAmbient, Real.cos_add_two_pi,
      Real.sin_add_two_pi]
  · simp [latitudePoint, hu]

private lemma angle_shift (f : ℝ → ℝ) (hf : Function.Periodic f (2 * Real.pi))
    (θ : ℝ) :
    (∫ t, f (θ + t) ∂angleMeasure) = ∫ t, f t ∂angleMeasure := by
  rw [angleMeasure, integral_smul_measure, integral_smul_measure]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity),
    ← intervalIntegral.integral_of_le (by positivity)]
  simp_rw [add_comm θ]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm θ] using hf.intervalIntegral_add_eq θ 0

private lemma latitude_surjective (y : Sphere) :
    ∃ θ : ℝ, latitudePoint (.refl ℝ Ambient)
      ((1 - (y : Ambient) 0) / 2) θ = y := by
  let u := (1 - (y : Ambient) 0) / 2
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨hlo, hhi⟩ := RawSphereProjection.coordinate_bound y 0
    constructor <;> dsimp [u] <;> linarith
  let z : ℂ := ⟨(y : Ambient) 1, (y : Ambient) 2⟩
  have hn : ‖z‖ = Real.sqrt (4*u*(1-u)) := by
    have hy := mem_sphere_zero_iff_norm.mp y.property
    have hs : (y : Ambient) 0 ^ 2 + ((y : Ambient) 1 ^ 2 + (y : Ambient) 2 ^ 2) = 1 := by
      have h := congrArg (fun t : ℝ => t ^ 2) hy
      rw [EuclideanSpace.real_norm_sq_eq] at h
      simpa [Fin.sum_univ_succ] using h
    rw [Complex.norm_def]
    congr 1
    simp only [Complex.normSq, z]
    dsimp [u]
    ring_nf at hs ⊢
    nlinarith
  refine ⟨z.arg, ?_⟩
  apply Subtype.ext
  rw [latitudePoint_val _ _ _ hu]
  ext i
  fin_cases i
  · simp [latitudeAmbient, u]
    ring
  · simpa [latitudeAmbient, ← hn, z] using Complex.norm_mul_cos_arg z
  · simpa [latitudeAmbient, ← hn, z] using Complex.norm_mul_sin_arg z

private lemma spin_preserving (t : ℝ) :
    MeasurePreserving (RawSphereProjection.rotation (spin t)) sphereArea sphereArea := by
  exact (RawSphereProjection.rotation_preserving (spin t)).smul_measure _

private lemma spin_rotation_measurable :
    Measurable (fun z : Sphere × ℝ => RawSphereProjection.rotation (spin z.2) z.1) := by
  suffices hm : Measurable (fun z : Sphere × ℝ =>
      (RawSphereProjection.rotation (spin z.2) z.1 : Ambient)) from hm.subtype_mk
  simp only [RawSphereProjection.rotation, spin_apply]
  fun_prop

private lemma bounded_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (f : Sphere →ᵇ ℝ) (p : X → Sphere) (hp : Measurable p) :
    Integrable (fun x => f (p x)) μ := by
  apply Integrable.mono' (integrable_const ‖f‖)
    (f.continuous.measurable.comp hp).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => f.norm_coe_le_norm (p x)

private lemma angle_mass : angleMeasure Set.univ = 1 := by
  rw [angleMeasure, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    Real.volume_Icc, sub_zero]
  exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)

private lemma latitude_integral (f : Sphere →ᵇ ℝ) :
    (∫ z : ℝ × ℝ, f (latitudePoint (.refl ℝ Ambient) z.1 z.2)
      ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod angleMeasure)) =
      ∫ y : Sphere, f y ∂sphereArea := by
  letI := sphereArea_isProbabilityMeasure
  let p : Sphere → ℝ := fun y => (1 - (y : Ambient) 0) / 2
  let A : ℝ → ℝ := fun u => ∫ t, f (latitudePoint (.refl ℝ Ambient) u t) ∂angleMeasure
  have hlat : Measurable (fun z : ℝ × ℝ => f (latitudePoint (.refl ℝ Ambient) z.1 z.2)) :=
    f.continuous.measurable.comp (latitudePoint_measurable _)
  have hA : StronglyMeasurable A := hlat.stronglyMeasurable.integral_prod_right'
  have hp : Measurable p := by dsimp [p]; fun_prop
  have hmap : Measure.map p sphereArea = volume.restrict (Set.Icc (0 : ℝ) 1) :=
    RawSphereProjection.normalized_coordinate_projection
  rw [integral_prod _ (bounded_integrable _ f _ (latitudePoint_measurable _))]
  change (∫ u, A u ∂volume.restrict (Set.Icc 0 1)) = _
  rw [← hmap, integral_map hp.aemeasurable hA.aestronglyMeasurable]
  have havg (y : Sphere) : A (p y) =
      ∫ t, f (RawSphereProjection.rotation (spin t) y) ∂angleMeasure := by
    obtain ⟨θ, hθ⟩ := latitude_surjective y
    conv_rhs => rw [← hθ]
    simp_rw [latitude_spin]
    exact (angle_shift (fun t => f (latitudePoint (.refl ℝ Ambient) (p y) t))
      ((latitude_periodic (p y)).comp f) θ).symm
  simp_rw [havg]
  have hi : Integrable (fun z : Sphere × ℝ =>
      f (RawSphereProjection.rotation (spin z.2) z.1)) (sphereArea.prod angleMeasure) :=
    bounded_integrable _ f _ spin_rotation_measurable
  rw [integral_integral_swap hi]
  have he (t : ℝ) : (∫ y : Sphere, f (RawSphereProjection.rotation (spin t) y) ∂sphereArea) =
      ∫ y : Sphere, f y ∂sphereArea :=
    by
      have h := integral_map (spin_preserving t).measurable.aemeasurable
        (f.continuous.aestronglyMeasurable (μ := Measure.map
          (RawSphereProjection.rotation (spin t)) sphereArea))
      rw [(spin_preserving t).map_eq] at h
      exact h.symm
  simp_rw [he]
  rw [integral_const, Measure.real, angle_mass]
  simp

private lemma latitude_disintegration_identity :
    MeasurePreserving (fun z : ℝ × ℝ => latitudePoint (.refl ℝ Ambient) z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod angleMeasure) sphereArea := by
  letI := sphereArea_isProbabilityMeasure
  refine ⟨latitudePoint_measurable _, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (latitudePoint_measurable _).aemeasurable
    f.continuous.aestronglyMeasurable]
  exact latitude_integral f

theorem latitude_disintegration (g : Ambient ≃ₗᵢ[ℝ] Ambient) :
    MeasurePreserving (fun z : ℝ × ℝ => latitudePoint g z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod angleMeasure) sphereArea := by
  have hg : MeasurePreserving (RawSphereProjection.rotation g) sphereArea sphereArea :=
    (RawSphereProjection.rotation_preserving g).smul_measure _
  convert hg.comp latitude_disintegration_identity using 1
  funext z
  apply Subtype.ext
  by_cases hu : z.1 ∈ Set.Icc (0 : ℝ) 1
  · simp [latitudePoint_val _ _ _ hu, RawSphereProjection.rotation, latitudeAmbient]
  · change (latitudePoint g z.1 z.2 : Ambient) =
      g (latitudePoint (.refl ℝ Ambient) z.1 z.2 : Ambient)
    simp only [latitudePoint, dif_neg hu]
    rfl

noncomputable def rotationVector (i : Fin 3) (x : Ambient) : Ambient :=
  WithLp.toLp 2 (fun j : Fin 3 =>
    if j = i + 1 then -x (i + 2) else if j = i + 2 then x (i + 1) else 0)

noncomputable def sphereOrthogonal (e : Ambient ≃ₗᵢ[ℝ] Ambient) : Sphere ≃ₜ Sphere :=
  e.toHomeomorph.subtype (fun x => by
    change ‖x - 0‖ = 1 ↔ ‖e x - 0‖ = 1
    simp only [sub_zero, e.norm_map])
@[simp] theorem sphereOrthogonal_coe (e : Ambient ≃ₗᵢ[ℝ] Ambient) (x : Sphere) :
    (sphereOrthogonal e x : Ambient) = e x := rfl

noncomputable def rotationFlowMap (i : Fin 3) (t : ℝ) : Ambient →ₗ[ℝ] Ambient where
  toFun x := WithLp.toLp 2 (fun j : Fin 3 =>
    if j = i then x i else if j = i + 1 then
      Real.cos t * x (i+1) - Real.sin t * x (i+2)
    else Real.sin t * x (i+1) + Real.cos t * x (i+2))
  map_add' x y := by ext j; simp only [PiLp.toLp_apply, PiLp.add_apply]; split_ifs <;> ring
  map_smul' c x := by ext j; simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

theorem rotationFlowMap_inverse (i : Fin 3) (t : ℝ) (x : Ambient) :
    rotationFlowMap i (-t) (rotationFlowMap i t x) = x := by
  have ht := Real.cos_sq_add_sin_sq t
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [rotationFlowMap, Fin.reduceAdd, Real.sin_neg, Real.cos_neg] <;>
    nlinarith [congrArg (fun a : ℝ => a * x 0) ht,
      congrArg (fun a : ℝ => a * x 1) ht,
      congrArg (fun a : ℝ => a * x 2) ht]

theorem rotationFlowMap_norm (i : Fin 3) (t : ℝ) (x : Ambient) :
    ‖rotationFlowMap i t x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have ht := Real.cos_sq_add_sin_sq t
  fin_cases i <;> simp only [Fin.sum_univ_three, rotationFlowMap, LinearMap.coe_mk,
    AddHom.coe_mk, PiLp.toLp_apply, Fin.reduceAdd, Real.norm_eq_abs, sq_abs] <;>
    simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

noncomputable def rotationFlow (i : Fin 3) (t : ℝ) : Ambient ≃ₗᵢ[ℝ] Ambient where
  toLinearEquiv :=
    { rotationFlowMap i t with
      invFun := rotationFlowMap i (-t)
      left_inv := rotationFlowMap_inverse i t
      right_inv := fun x => by
        change rotationFlowMap i t (rotationFlowMap i (-t) x) = x
        simpa only [neg_neg] using rotationFlowMap_inverse i (-t) x }
  norm_map' := rotationFlowMap_norm i t

@[simp] theorem rotationFlow_apply (i : Fin 3) (t : ℝ) (x : Ambient) :
    rotationFlow i t x = rotationFlowMap i t x := rfl
@[simp] theorem rotationFlow_zero (i : Fin 3) (x : Ambient) : rotationFlow i 0 x = x := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [rotationFlowMap, rotationFlow, Fin.reduceAdd]
theorem rotationFlow_hasDerivAt (i : Fin 3) (x : Ambient) (t : ℝ) :
    HasDerivAt (fun t => rotationFlow i t x) (rotationVector i (rotationFlow i t x)) t := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hp : HasDerivAt (fun t => (rotationFlow i t x).ofLp)
      ((rotationVector i (rotationFlow i t x)).ofLp) t := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [rotationFlow_apply, rotationFlowMap, rotationVector, Fin.reduceAdd]
    all_goals
      first
      | exact hasDerivAt_const t _
      | convert ((Real.hasDerivAt_cos t).mul_const _).sub ((Real.hasDerivAt_sin t).mul_const _) using 1 <;> ring
      | convert ((Real.hasDerivAt_sin t).mul_const _).add ((Real.hasDerivAt_cos t).mul_const _) using 1 <;> ring
  exact e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hp

namespace CircleAverage
open MvPolynomial
private lemma shift (f : ℝ → ℂ) (hf : Function.Periodic f (2 * Real.pi)) (θ : ℝ) :
    (∫ t, f (θ + t) ∂angleMeasure) = ∫ t, f t ∂angleMeasure := by
  rw [angleMeasure, integral_smul_measure, integral_smul_measure]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity),
    ← intervalIntegral.integral_of_le (by positivity)]
  simp_rw [add_comm θ]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm θ] using hf.intervalIntegral_add_eq θ 0
noncomputable def moment (i j : ℕ) : ℂ :=
  ∫ θ : ℝ, (Real.cos θ : ℂ)^i * (Real.sin θ : ℂ)^j ∂angleMeasure
private lemma moment_odd (i j : ℕ) (h : Odd (i+j)) : moment i j = 0 := by
  let f : ℝ → ℂ := fun θ => (Real.cos θ : ℂ)^i * (Real.sin θ : ℂ)^j
  have hp : Function.Periodic f (2*Real.pi) := by
    intro θ
    dsimp only [f]
    rw [Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hn (θ : ℝ) : f (Real.pi + θ) = - f θ := by
    dsimp only [f]
    rw [add_comm Real.pi, Real.cos_add_pi, Real.sin_add_pi]
    simp only [Complex.ofReal_neg]
    rw [neg_eq_neg_one_mul (Real.cos θ : ℂ), neg_eq_neg_one_mul (Real.sin θ : ℂ),
      mul_pow, mul_pow]
    calc
      (-1 : ℂ)^i * (Real.cos θ : ℂ)^i * ((-1 : ℂ)^j * (Real.sin θ : ℂ)^j) =
          (-1 : ℂ)^(i+j) * ((Real.cos θ : ℂ)^i * (Real.sin θ : ℂ)^j) := by rw [pow_add]; ring
      _ = - ((Real.cos θ : ℂ)^i * (Real.sin θ : ℂ)^j) := by rw [h.neg_one_pow]; ring
  have he := shift f hp Real.pi
  simp_rw [hn] at he
  rw [integral_neg] at he
  change -moment i j = moment i j at he
  linear_combination -he / 2
private lemma mono_formula (d : Fin 3 →₀ ℕ) (a : ℂ) (u θ : ℝ)
    (hu : u ∈ Set.Icc (0:ℝ) 1) :
    polynomialSphere (MvPolynomial.monomial d a) (latitudePoint (.refl ℝ Ambient) u θ) =
      a * ((1-2*u : ℝ):ℂ)^(d 0) * (Real.sqrt (4*u*(1-u)) : ℂ)^(d 1+d 2) *
        ((Real.cos θ : ℂ)^(d 1) * (Real.sin θ : ℂ)^(d 2)) := by
  rw [polynomialSphere, MvPolynomial.eval_monomial, latitudePoint_val _ _ _ hu]
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp [latitudeAmbient, Fin.prod_univ_succ, mul_pow, pow_add]
  ring
private lemma mono_integral (d : Fin 3 →₀ ℕ) (a : ℂ) (u : ℝ)
    (hu : u ∈ Set.Icc (0:ℝ) 1) :
    (∫ θ : ℝ, polynomialSphere (MvPolynomial.monomial d a)
      (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) =
      a * ((1-2*u : ℝ):ℂ)^(d 0) * (Real.sqrt (4*u*(1-u)) : ℂ)^(d 1+d 2) * moment (d 1) (d 2) := by
  simp_rw [mono_formula d a u _ hu]
  exact integral_const_mul _ _
private lemma poly_integrable (p : MvPolynomial (Fin 3) ℂ) (u : ℝ)
    (hu : u ∈ Set.Icc (0:ℝ) 1) :
    Integrable (fun θ => polynomialSphere p (latitudePoint (.refl ℝ Ambient) u θ)) angleMeasure := by
  have hc : Continuous (fun θ => polynomialSphere p (latitudePoint (.refl ℝ Ambient) u θ)) := by
    simp only [polynomialSphere, latitudePoint_val _ _ _ hu]
    apply (MvPolynomial.continuous_eval p).comp
    apply continuous_pi
    intro i
    fin_cases i <;> change Continuous _ <;> dsimp [latitudeAmbient]
    all_goals fun_prop
  exact (hc.integrableOn_Icc).smul_measure (by simp [ENNReal.inv_ne_top]; positivity)
private lemma exists_profile (p : MvPolynomial (Fin 3) ℂ) :
    ∃ Q : Polynomial ℂ, ∀ u : ℝ, u ∈ Set.Icc (0:ℝ) 1 →
      (∫ θ : ℝ, polynomialSphere p (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) = Q.eval (u:ℂ) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    rcases Nat.even_or_odd (d 1 + d 2) with he | ho
    · obtain ⟨k, hk⟩ := he
      refine ⟨Polynomial.C (a * moment (d 1) (d 2)) *
        (1 - Polynomial.C 2 * Polynomial.X)^(d 0) *
        (Polynomial.C 4 * Polynomial.X * (1-Polynomial.X))^k, ?_⟩
      intro u hu
      rw [mono_integral d a u hu]
      have hs : (Real.sqrt (4*u*(1-u)) : ℂ)^(d 1+d 2) = ((4*u*(1-u) : ℝ):ℂ)^k := by
        rw [hk, ← two_mul, pow_mul]
        rw [← Complex.ofReal_pow, Real.sq_sqrt (by nlinarith [hu.1, hu.2])]
      rw [hs]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
        Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
      ring
    · refine ⟨0, ?_⟩
      intro u hu
      rw [mono_integral d a u hu, moment_odd _ _ ho]
      simp
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hq
    refine ⟨P+Q, ?_⟩
    intro u hu
    simp only [polynomialSphere, map_add]
    change (∫ θ : ℝ, polynomialSphere p (latitudePoint (.refl ℝ Ambient) u θ) +
      polynomialSphere q (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) = _
    rw [integral_add (poly_integrable p u hu) (poly_integrable q u hu)]
    exact (congrArg₂ (· + ·) (hP u hu) (hQ u hu)).trans (Polynomial.eval_add).symm

theorem latitude_average_polynomial (p : MvPolynomial (Fin 3) ℂ) :
    ∃ Q : Polynomial ℂ,
      (∀ (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
        (∫ θ : ℝ, polynomialSphere p
          (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) = Q.eval (u : ℂ)) ∧
      Q.eval 0 = polynomialSphere p
        ⟨north, mem_sphere_zero_iff_norm.mpr north_norm⟩ := by
  obtain ⟨Q,hQ⟩ := exists_profile p
  refine ⟨Q,hQ,?_⟩
  have hm : angleMeasure Set.univ = 1 := by
    rw [angleMeasure, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Icc]
    simp only [sub_zero, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)
  have hz (θ : ℝ) : latitudePoint (.refl ℝ Ambient) 0 θ =
      ⟨north, mem_sphere_zero_iff_norm.mpr north_norm⟩ := by
    apply Subtype.ext
    rw [latitudePoint_val _ _ _ (by constructor <;> norm_num)]
    ext i
    fin_cases i <;> simp [latitudeAmbient, north, PiLp.single_apply]
  have he := hQ 0 (by constructor <;> norm_num)
  simp only [hz, Complex.ofReal_zero, integral_const, Measure.real, hm,
    ENNReal.toReal_one, one_smul] at he
  exact he.symm

noncomputable def rot (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :=
  X (i + 1) * pderiv (i + 2) p - X (i + 2) * pderiv (i + 1) p
noncomputable def euler (p : MvPolynomial (Fin 3) ℂ) :=
  ∑ i : Fin 3, X i * pderiv i p
noncomputable def casOp (p : MvPolynomial (Fin 3) ℂ) :=
  -(∑ i : Fin 3, rot i (rot i p))
private theorem casimir (p : MvPolynomial (Fin 3) ℂ) :
    casOp p = euler (euler p) + euler p -
      (∑ i : Fin 3, X i ^ 2) * polynomialLaplacian p := by
  simp only [casOp, rot, euler, polynomialLaplacian, Fin.sum_univ_three,
    LinearMap.add_apply, LinearMap.comp_apply, Derivation.coeFn_coe,
    map_add, map_sub, pderiv_mul, Fin.reduceAdd, pderiv_X, Pi.single_apply]
  norm_num
  ring
private theorem casOp_eigen (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) :
    casOp p = ((ℓ : ℂ) * ((ℓ : ℂ) + 1)) • p := by
  have he : euler p = ℓ • p :=
    (MvPolynomial.mem_homogeneousSubmodule ℓ p).mp hp.1 |>.sum_X_mul_pderiv
  have hee : euler (euler p) = ℓ • (ℓ • p) := by
    calc
      euler (euler p) = euler (ℓ • p) := by rw [he]
      _ = ℓ • euler p := by
        simp only [euler, Fin.sum_univ_three, map_nsmul]
        simp only [nsmul_eq_mul]
        ring
      _ = ℓ • (ℓ • p) := by rw [he]
  have hl : polynomialLaplacian p = 0 := hp.2
  rw [casimir, hee, he, hl, mul_zero, sub_zero]
  simp only [nsmul_eq_mul, smul_eq_C_mul, map_mul, map_add, map_natCast, map_one]
  ring
private theorem rot_X (i j : Fin 3) (x : Ambient) :
    eval (fun k => (x k : ℂ)) (rot i (X j)) = ((rotationVector i x) j : ℂ) := by
  fin_cases i <;> fin_cases j <;>
    simp [rot, pderiv_X, Pi.single_apply, rotationVector, Fin.reduceAdd]
private theorem rot_eval_flow (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ)
    (x : Ambient) (t : ℝ) :
    HasDerivAt (fun t => eval (fun j => ((rotationFlow i t x) j : ℂ)) p)
      (eval (fun j => ((rotationFlow i t x) j : ℂ)) (rot i p)) t := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa [rot] using (hasDerivAt_const t a)
  | add p q hp hq =>
    have hd := hp.add hq
    change HasDerivAt (fun t => eval _ p + eval _ q) _ t at hd
    convert hd using 1
    · simp only [map_add]
    · simp only [rot, map_add, map_sub, map_mul, eval_X]
      ring
  | mul_X p j hp =>
    have hj := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      ((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp_hasDerivAt t
        (rotationFlow_hasDerivAt i x t))
    change HasDerivAt (fun t => ((rotationFlow i t x) j : ℂ))
      ((rotationVector i (rotationFlow i t x)) j : ℂ) t at hj
    have hd := hp.mul hj
    change HasDerivAt (fun t => eval _ p * ((rotationFlow i t x) j : ℂ)) _ t at hd
    convert hd using 1
    · simp only [map_mul, eval_X]
    · rw [← rot_X i j (rotationFlow i t x)]
      simp only [rot, pderiv_mul, map_sub, map_add, map_mul, eval_X]
      ring
private theorem rot_zero (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ)
    (h : ∀ x : Sphere, polynomialSphere p x = 0) :
    ∀ x : Sphere, polynomialSphere (rot i p) x = 0 := by
  intro x
  have hd := rot_eval_flow i p (x : Ambient) 0
  have he : (fun t => eval (fun j => ((rotationFlow i t (x : Ambient)) j : ℂ)) p) =
      (fun _ : ℝ => (0 : ℂ)) := by
    funext t
    exact h (sphereOrthogonal (rotationFlow i t) x)
  rw [he] at hd
  simpa only [rotationFlow_zero, polynomialSphere] using hd.unique (hasDerivAt_const 0 (0 : ℂ))
private theorem casOp_zero (p : MvPolynomial (Fin 3) ℂ)
    (h : ∀ x : Sphere, polynomialSphere p x = 0) :
    ∀ x : Sphere, polynomialSphere (casOp p) x = 0 := by
  intro x
  simp only [polynomialSphere, casOp, map_neg, map_sum]
  rw [Finset.sum_eq_zero]
  · simp
  · intro i hi
    exact rot_zero i (rot i p) (rot_zero i p h) x
noncomputable def heightLift : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  Polynomial.aeval ((1 - X 0) * C (1 / 2))
private theorem pderiv_heightLift (i : Fin 3) (Q : Polynomial ℂ) :
    pderiv i (heightLift Q) = (if i = 0 then C (-1 / 2) else 0) *
      heightLift Q.derivative := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.derivative_add, hp, hq, mul_add]
  | monomial n a =>
    simp only [heightLift, Polynomial.aeval_monomial, Polynomial.derivative_monomial,
      Polynomial.aeval_C, Polynomial.aeval_mul, map_pow, Polynomial.aeval_X, algebraMap_eq]
    rw [pderiv_C_mul, pderiv_pow]
    have hx : pderiv i ((1 - X 0) * C (1 / 2 : ℂ)) = if i = 0 then C (-1 / 2 : ℂ) else 0 := by
      by_cases hi : i = 0
      · subst i; simp [div_eq_mul_inv]
      · simp [pderiv_mul, pderiv_X, Pi.single_apply, hi, Ne.symm hi]
    simp only [hx, map_mul, map_natCast]
    by_cases hi : i = 0 <;> simp [hi] <;> ring
private theorem casOp_heightLift (Q : Polynomial ℂ) :
    casOp (heightLift Q) =
      -(X 1 ^ 2 + X 2 ^ 2) * C (1 / 4) * heightLift Q.derivative.derivative -
        X 0 * heightLift Q.derivative := by
  simp only [casOp, rot, Fin.sum_univ_three, Fin.reduceAdd, pderiv_heightLift,
    pderiv_mul, map_sub, pderiv_X, Pi.single_apply, pderiv_C]
  norm_num
  have hc : C (1 / 2 : ℂ) ^ 2 = (C (1 / 4 : ℂ) : MvPolynomial (Fin 3) ℂ) := by
    rw [← map_pow]; congr 1; norm_num
  have ht : C (1 / 2 : ℂ) * 2 = (1 : MvPolynomial (Fin 3) ℂ) := by
    rw [show (2 : MvPolynomial (Fin 3) ℂ) = C (2 : ℂ) by exact (map_ofNat C 2).symm, ← map_mul]; norm_num
  linear_combination -(X 0 * heightLift Q.derivative) * ht -
    ((X 1 ^ 2 + X 2 ^ 2) * heightLift Q.derivative.derivative) * hc
private theorem casOp_sub (p q : MvPolynomial (Fin 3) ℂ) :
    casOp (p - q) = casOp p - casOp q := by
  simp only [casOp, rot, map_sub, mul_sub, Fin.sum_univ_three]
  ring
private theorem eval_heightLift (Q : Polynomial ℂ) (x : Fin 3 → ℂ) :
    eval x (heightLift Q) = Q.eval ((1 - x 0) / 2) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | monomial n a => simp [heightLift, Polynomial.aeval_monomial, div_eq_mul_inv]
private theorem sphere_radius (x : Sphere) :
    ((x : Ambient) 0 : ℂ) ^ 2 + ((x : Ambient) 1 : ℂ) ^ 2 +
      ((x : Ambient) 2 : ℂ) ^ 2 = 1 := by
  have hn := mem_sphere_zero_iff_norm.mp x.property
  have h := congrArg (fun t : ℝ => t ^ 2) hn
  rw [EuclideanSpace.real_norm_sq_eq] at h
  norm_num [Fin.sum_univ_three] at h
  exact_mod_cast h

theorem zonal_harmonic_legendre_ode (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) (Q : Polynomial ℂ)
    (hQ : ∀ x : Sphere, polynomialSphere p x =
      Q.eval ((1 - ((x : Ambient) 0 : ℂ)) / 2)) :
    Polynomial.X * (1 - Polynomial.X) * Q.derivative.derivative +
      (1 - 2 * Polynomial.X) * Q.derivative +
      Polynomial.C ((ℓ : ℂ) * ((ℓ : ℂ) + 1)) * Q = 0 := by
  have hz : ∀ x : Sphere, polynomialSphere (casOp (p - heightLift Q)) x = 0 :=
    casOp_zero _ (by
      intro x
      simp only [polynomialSphere, map_sub, eval_heightLift]
      exact sub_eq_zero.mpr (hQ x))
  have he (x : Sphere) :
      let u : ℂ := (1 - ((x : Ambient) 0 : ℂ)) / 2
      u * (1 - u) * Q.derivative.derivative.eval u +
        (1 - 2 * u) * Q.derivative.eval u +
        ((ℓ : ℂ) * ((ℓ : ℂ) + 1)) * Q.eval u = 0 := by
    have hx := hz x
    rw [casOp_sub, casOp_eigen ℓ p hp, casOp_heightLift] at hx
    simp only [polynomialSphere, map_sub, map_mul, map_add, map_neg, map_pow,
      eval_C, eval_X, smul_eq_C_mul, eval_heightLift] at hx
    rw [show eval (fun i => ((x : Ambient) i : ℂ)) p = _ from hQ x] at hx
    have hr := sphere_radius x
    dsimp
    linear_combination hx - (Q.derivative.derivative.eval
      ((1 - ((x : Ambient) 0 : ℂ)) / 2) / 4) * hr
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.Infinite.mono (s := Complex.ofReal '' Set.Icc (0 : ℝ) 1)
  · intro z hz
    obtain ⟨u, hu, rfl⟩ := hz
    have hh := he (latitudePoint (.refl ℝ Ambient) u 0)
    have hc : ((latitudePoint (.refl ℝ Ambient) u 0 : Ambient) 0 : ℂ) = 1 - 2 * (u : ℂ) := by
      rw [latitudePoint_val _ _ _ hu]
      simp [latitudeAmbient, Complex.ofReal_sub, Complex.ofReal_mul]
    dsimp at hh
    rw [hc, show (1 - (1 - 2 * (u : ℂ))) / 2 = (u : ℂ) by ring] at hh
    simpa [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul] using hh
  · exact (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image
      Complex.ofReal_injective.injOn

noncomputable def spinSubst (A : Matrix (Fin 3) (Fin 3) ℂ) :
    MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j)

private theorem pderiv_spinSubst (A : Matrix (Fin 3) (Fin 3) ℂ)
    (p : MvPolynomial (Fin 3) ℂ) (j : Fin 3) :
    MvPolynomial.pderiv j (spinSubst A p) =
      ∑ i, MvPolynomial.C (A i j) * spinSubst A (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [spinSubst]
  | add p q ihp ihq =>
      simp only [map_add, ihp, ihq, mul_add, Finset.sum_add_distrib]
  | mul_X p i ih =>
      simp only [map_mul, spinSubst, MvPolynomial.aeval_X]
      rw [MvPolynomial.pderiv_mul]
      simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
        map_add, map_mul, map_sum, MvPolynomial.pderiv_C, zero_mul, zero_add]
      unfold spinSubst at ih
      rw [ih]
      simp [Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib,
        Pi.single_apply, mul_add, mul_ite, mul_assoc, mul_comm, mul_left_comm]

private theorem polynomialLaplacian_spinSubst (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ i k, ∑ j, A i j * A k j = if i = k then 1 else 0)
    (p : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (spinSubst A p) = spinSubst A (polynomialLaplacian p) := by
  classical
  simp only [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    map_sum]
  change (∑ j, MvPolynomial.pderiv j (MvPolynomial.pderiv j (spinSubst A p))) =
    ∑ j, spinSubst A (MvPolynomial.pderiv j (MvPolynomial.pderiv j p))
  simp only [pderiv_spinSubst, map_sum, MvPolynomial.pderiv_C_mul]
  simp only [pderiv_spinSubst, Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum]
  simp_rw [hA]
  simp

private theorem spinSubst_homogeneous (A : Matrix (Fin 3) (Fin 3) ℂ)
    (p : MvPolynomial (Fin 3) ℂ) (ℓ : ℕ) (hp : p.IsHomogeneous ℓ) :
    (spinSubst A p).IsHomogeneous ℓ := by
  unfold spinSubst
  simpa using hp.aeval (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j)
    (fun i => MvPolynomial.IsHomogeneous.sum _ _ 1 (fun j _ =>
      MvPolynomial.isHomogeneous_C_mul_X _ _))

private theorem spinSubst_harmonic (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ i k, ∑ j, A i j * A k j = if i = k then 1 else 0)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ harmonicPolynomials ℓ) :
    spinSubst A p ∈ harmonicPolynomials ℓ := by
  refine ⟨spinSubst_homogeneous A p ℓ hp.1, ?_⟩
  change polynomialLaplacian (spinSubst A p) = 0
  rw [polynomialLaplacian_spinSubst A hA]
  have hh : polynomialLaplacian p = 0 := hp.2
  rw [hh, map_zero]

noncomputable def spinMatrix (t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![1,0,0], ![0,(Real.cos t : ℂ),-(Real.sin t : ℂ)],
    ![0,(Real.sin t : ℂ),(Real.cos t : ℂ)]]
private theorem spinMatrix_orthogonal (t : ℝ) (i k : Fin 3) :
    ∑ j, spinMatrix t i j * spinMatrix t k j = if i = k then 1 else 0 := by
  have h : (Real.cos t : ℂ)^2 + (Real.sin t : ℂ)^2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq t
  simp only [Complex.ofReal_cos, Complex.ofReal_sin] at h
  fin_cases i <;> fin_cases k <;> simp [spinMatrix, Fin.sum_univ_three] <;>
    (first | (solve | ring) | (linear_combination h))
private theorem spinSubst_eval (t : ℝ) (p : MvPolynomial (Fin 3) ℂ) (x : Ambient) :
    eval (fun j => (x j : ℂ)) (spinSubst (spinMatrix t) p) =
      eval (fun j => ((rotationFlow 0 t x) j : ℂ)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [spinSubst]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, spinSubst, aeval_X, map_sum, eval_C, eval_X]
    congr 1
    fin_cases i <;> simp [spinMatrix, Fin.sum_univ_three, rotationFlowMap,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul] <;> ring
instance sphere_compact : CompactSpace Sphere :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient) 1)
noncomputable def polyCM : MvPolynomial (Fin 3) ℂ →ₗ[ℂ] C(Sphere, ℂ) where
  toFun p := ⟨polynomialSphere p, (MvPolynomial.continuous_eval p).comp (by fun_prop)⟩
  map_add' p q := by ext x; change polynomialSphere (p + q) x = polynomialSphere p x + polynomialSphere q x; simp [polynomialSphere]
  map_smul' c p := by ext x; change polynomialSphere (c • p) x = c • polynomialSphere p x; simp [polynomialSphere]
noncomputable def spinCM (p : MvPolynomial (Fin 3) ℂ) (t : ℝ) : C(Sphere, ℂ) :=
  ⟨fun x => polynomialSphere p (sphereOrthogonal (rotationFlow 0 t) x),
    (polyCM p).continuous.comp (sphereOrthogonal (rotationFlow 0 t)).continuous⟩
private theorem spinCM_continuous (p : MvPolynomial (Fin 3) ℂ) : Continuous (spinCM p) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun tx : ℝ × Sphere => eval
    (fun j => ((rotationFlow 0 tx.1 (tx.2 : Ambient)) j : ℂ)) p)
  apply (MvPolynomial.continuous_eval p).comp
  apply continuous_pi
  intro j
  fin_cases j <;> simp [rotationFlowMap] <;> fun_prop
private theorem spinCM_integrable (p : MvPolynomial (Fin 3) ℂ) :
    Integrable (spinCM p) angleMeasure :=
  (spinCM_continuous p).integrableOn_Icc.smul_measure (by
    simp [ENNReal.inv_ne_top]; positivity)
private theorem average_harmonic (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) :
    ∃ q ∈ harmonicPolynomials ℓ, ∀ x : Sphere,
      polynomialSphere q x = ∫ t, polynomialSphere p
        (sphereOrthogonal (rotationFlow 0 t) x) ∂angleMeasure := by
  classical
  let H := (harmonicPolynomials ℓ).map polyCM
  haveI : Module.Finite ℂ (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ ℓ)
  haveI : FiniteDimensional ℂ (harmonicPolynomials ℓ) :=
    Submodule.finiteDimensional_of_le (show harmonicPolynomials ℓ ≤
      MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ from inf_le_left)
  haveI : FiniteDimensional ℂ H := inferInstance
  have hm (t : ℝ) : spinCM p t ∈ H := by
    refine ⟨spinSubst (spinMatrix t) p,
      spinSubst_harmonic _ (spinMatrix_orthogonal t) ℓ p hp, ?_⟩
    ext x
    exact spinSubst_eval t p x
  have hmass : angleMeasure Set.univ = 1 := by
    rw [angleMeasure, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Icc]
    simp only [sub_zero, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)
  letI : IsProbabilityMeasure angleMeasure := ⟨hmass⟩
  have hmem : (∫ t, spinCM p t ∂angleMeasure) ∈ H :=
    (H.restrictScalars ℝ).convex.integral_mem H.closed_of_finiteDimensional
      (Filter.Eventually.of_forall hm) (spinCM_integrable p)
  obtain ⟨q, hq, he⟩ := hmem
  refine ⟨q, hq, fun x => ?_⟩
  have hex := congrArg (fun f : C(Sphere, ℂ) => f x) he
  exact hex.trans (ContinuousMap.integral_apply (spinCM_integrable p) x)

private lemma latitude_surjective_aux (y : Sphere) :
    ∃ θ : ℝ, latitudePoint (.refl ℝ Ambient)
      ((1 - (y : Ambient) 0) / 2) θ = y := by
  let u := (1 - (y : Ambient) 0) / 2
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨hlo, hhi⟩ := RawSphereProjection.coordinate_bound y 0
    constructor <;> dsimp [u] <;> linarith
  let z : ℂ := ⟨(y : Ambient) 1, (y : Ambient) 2⟩
  have hn : ‖z‖ = Real.sqrt (4*u*(1-u)) := by
    have hy := mem_sphere_zero_iff_norm.mp y.property
    have hs : (y : Ambient) 0 ^ 2 + ((y : Ambient) 1 ^ 2 + (y : Ambient) 2 ^ 2) = 1 := by
      have h := congrArg (fun t : ℝ => t ^ 2) hy
      rw [EuclideanSpace.real_norm_sq_eq] at h
      simpa [Fin.sum_univ_succ] using h
    rw [Complex.norm_def]
    congr 1
    simp only [Complex.normSq, z]
    dsimp [u]
    ring_nf at hs ⊢
    nlinarith
  refine ⟨z.arg, ?_⟩
  apply Subtype.ext
  rw [latitudePoint_val _ _ _ hu]
  ext i
  fin_cases i
  · simp [latitudeAmbient, u]
    ring
  · simpa [latitudeAmbient, ← hn, z] using Complex.norm_mul_cos_arg z
  · simpa [latitudeAmbient, ← hn, z] using Complex.norm_mul_sin_arg z

private lemma angle_shift_aux (f : ℝ → ℂ) (hf : Function.Periodic f (2 * Real.pi))
    (θ : ℝ) :
    (∫ t, f (θ + t) ∂angleMeasure) = ∫ t, f t ∂angleMeasure := by
  rw [angleMeasure, integral_smul_measure, integral_smul_measure]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity),
    ← intervalIntegral.integral_of_le (by positivity)]
  simp_rw [add_comm θ]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm θ] using hf.intervalIntegral_add_eq θ 0

private theorem latitude_flow (u θ t : ℝ) :
    sphereOrthogonal (rotationFlow 0 t) (latitudePoint (.refl ℝ Ambient) u θ) =
      latitudePoint (.refl ℝ Ambient) u (θ + t) := by
  apply Subtype.ext
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · simp only [sphereOrthogonal_coe, latitudePoint_val _ _ _ hu,
      latitudeAmbient, rotationFlow_apply, rotationFlowMap]
    ext i
    fin_cases i <;> simp [Real.cos_add, Real.sin_add] <;> ring
  · simp only [sphereOrthogonal_coe, latitudePoint, dif_neg hu]
    ext i
    fin_cases i <;> simp [rotationFlowMap, north, PiLp.single_apply]
private theorem latitude_periodic_aux (u : ℝ) :
    Function.Periodic (latitudePoint (.refl ℝ Ambient) u) (2 * Real.pi) := by
  intro θ
  apply Subtype.ext
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · simp [latitudePoint_val _ _ _ hu, latitudeAmbient, Real.cos_add_two_pi,
      Real.sin_add_two_pi]
  · simp [latitudePoint, hu]

theorem latitude_average_legendre_ode (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) (Q : Polynomial ℂ)
    (hQ : ∀ (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
      (∫ θ : ℝ, polynomialSphere p
        (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) = Q.eval (u : ℂ)) :
    Polynomial.X * (1 - Polynomial.X) * Q.derivative.derivative +
      (1 - 2 * Polynomial.X) * Q.derivative +
      Polynomial.C ((ℓ : ℂ) * ((ℓ : ℂ) + 1)) * Q = 0 := by
  obtain ⟨q, hq, havg⟩ := average_harmonic ℓ p hp
  apply zonal_harmonic_legendre_ode ℓ q hq Q
  intro x
  obtain ⟨θ, hθ⟩ := latitude_surjective_aux x
  let u : ℝ := (1 - (x : Ambient) 0) / 2
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨hlo, hhi⟩ := RawSphereProjection.coordinate_bound x 0
    constructor <;> dsimp [u] <;> linarith
  rw [havg x]
  have hflow (t : ℝ) : sphereOrthogonal (rotationFlow 0 t) x =
      latitudePoint (.refl ℝ Ambient) u (θ + t) := by
    rw [← hθ, latitude_flow]
  simp_rw [hflow]
  have hshift := angle_shift_aux _
    ((latitude_periodic_aux u).comp (polynomialSphere p)) θ
  simp only [Function.comp_apply] at hshift
  rw [hshift, hQ u hu]
  congr 1
  simp [u, Complex.ofReal_div, Complex.ofReal_sub]

end CircleAverage
noncomputable def linearSubstitution (A : Matrix (Fin 3) (Fin 3) ℂ) :
    MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j)

theorem pderiv_linearSubstitution (A : Matrix (Fin 3) (Fin 3) ℂ)
    (p : MvPolynomial (Fin 3) ℂ) (j : Fin 3) :
    MvPolynomial.pderiv j (linearSubstitution A p) =
      ∑ i, MvPolynomial.C (A i j) * linearSubstitution A (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [linearSubstitution]
  | add p q ihp ihq =>
      simp only [map_add, ihp, ihq, mul_add, Finset.sum_add_distrib]
  | mul_X p i ih =>
      simp only [map_mul, linearSubstitution, MvPolynomial.aeval_X]
      rw [MvPolynomial.pderiv_mul]
      simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
        map_add, map_mul, map_sum, MvPolynomial.pderiv_C, zero_mul, zero_add]
      unfold linearSubstitution at ih
      rw [ih]
      simp [Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib,
        Pi.single_apply, mul_add, mul_ite, mul_assoc, mul_comm, mul_left_comm]

theorem polynomialLaplacian_linearSubstitution (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ i k, ∑ j, A i j * A k j = if i = k then 1 else 0)
    (p : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (linearSubstitution A p) = linearSubstitution A (polynomialLaplacian p) := by
  classical
  simp only [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    map_sum]
  change (∑ j, MvPolynomial.pderiv j (MvPolynomial.pderiv j (linearSubstitution A p))) =
    ∑ j, linearSubstitution A (MvPolynomial.pderiv j (MvPolynomial.pderiv j p))
  simp only [pderiv_linearSubstitution, map_sum, MvPolynomial.pderiv_C_mul]
  simp only [pderiv_linearSubstitution, Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum]
  simp_rw [hA]
  simp

theorem linearSubstitution_homogeneous (A : Matrix (Fin 3) (Fin 3) ℂ)
    (p : MvPolynomial (Fin 3) ℂ) (ℓ : ℕ) (hp : p.IsHomogeneous ℓ) :
    (linearSubstitution A p).IsHomogeneous ℓ := by
  unfold linearSubstitution
  simpa using hp.aeval (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j)
    (fun i => MvPolynomial.IsHomogeneous.sum _ _ 1 (fun j _ =>
      MvPolynomial.isHomogeneous_C_mul_X _ _))

theorem linearSubstitution_harmonic (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ i k, ∑ j, A i j * A k j = if i = k then 1 else 0)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ harmonicPolynomials ℓ) :
    linearSubstitution A p ∈ harmonicPolynomials ℓ := by
  refine ⟨linearSubstitution_homogeneous A p ℓ hp.1, ?_⟩
  change polynomialLaplacian (linearSubstitution A p) = 0
  rw [polynomialLaplacian_linearSubstitution A hA]
  have hh : polynomialLaplacian p = 0 := hp.2
  rw [hh, map_zero]

noncomputable def orthogonalSubstitutionMatrix (g : Ambient ≃ₗᵢ[ℝ] Ambient) :
    Matrix (Fin 3) (Fin 3) ℂ := fun i j => (g.symm (EuclideanSpace.single i 1)) j

theorem orthogonalSubstitutionMatrix_orthogonal (g : Ambient ≃ₗᵢ[ℝ] Ambient) (i k : Fin 3) :
    ∑ j, orthogonalSubstitutionMatrix g i j * orthogonalSubstitutionMatrix g k j =
      if i = k then 1 else 0 := by
  simp only [orthogonalSubstitutionMatrix, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  have hh := g.symm.inner_map_map (EuclideanSpace.single i 1) (EuclideanSpace.single k 1)
  rw [PiLp.inner_apply] at hh
  simp only [RCLike.inner_apply, conj_trivial] at hh
  rw [show (∑ j, (g.symm (EuclideanSpace.single i 1)) j * (g.symm (EuclideanSpace.single k 1)) j) =
    inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single k 1) by
      simpa [mul_comm] using hh]
  by_cases h : i = k
  · subst k
    simp [EuclideanSpace.inner_single_left, PiLp.single_apply]
  · simp [EuclideanSpace.inner_single_left, PiLp.single_apply, h, Ne.symm h]

theorem orthogonalSubstitutionMatrix_eval (g : Ambient ≃ₗᵢ[ℝ] Ambient) (v : Ambient) (i : Fin 3) :
    ∑ j, orthogonalSubstitutionMatrix g i j * (v j : ℂ) = ((g v) i : ℂ) := by
  simp only [orthogonalSubstitutionMatrix, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1
  have hh := g.symm.inner_map_map (EuclideanSpace.single i 1) (g v)
  simp only [g.symm_apply_apply, EuclideanSpace.inner_single_left, mul_one] at hh
  rw [PiLp.inner_apply] at hh
  simp only [RCLike.inner_apply, conj_trivial] at hh
  simpa [mul_comm] using hh

theorem orthogonalSubstitution_eval (g : Ambient ≃ₗᵢ[ℝ] Ambient)
    (p : MvPolynomial (Fin 3) ℂ) (v : Ambient) :
    MvPolynomial.eval (fun j => (v j : ℂ)) (linearSubstitution (orthogonalSubstitutionMatrix g) p) =
      MvPolynomial.eval (fun i => ((g v) i : ℂ)) p := by
  unfold linearSubstitution
  change MvPolynomial.aeval (fun j => (v j : ℂ))
    (MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (orthogonalSubstitutionMatrix g i j) * MvPolynomial.X j) p) =
    MvPolynomial.aeval (fun i => ((g v) i : ℂ)) p
  rw [MvPolynomial.comp_aeval_apply]
  congr 2
  funext i
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.algebraMap_self]
  exact orthogonalSubstitutionMatrix_eval g v i

theorem orthogonalSubstitution_latitude (g : Ambient ≃ₗᵢ[ℝ] Ambient)
    (p : MvPolynomial (Fin 3) ℂ) (u θ : ℝ) :
    polynomialSphere (linearSubstitution (orthogonalSubstitutionMatrix g) p)
      (latitudePoint (.refl ℝ Ambient) u θ) = polynomialSphere p (latitudePoint g u θ) := by
  simp only [polynomialSphere, orthogonalSubstitution_eval]
  apply congrArg (fun v : Ambient => MvPolynomial.eval (fun i => (v i : ℂ)) p)
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · simp [latitudePoint_val _ _ _ hu, latitudeAmbient]
  · simp [latitudePoint, hu]

theorem harmonic_latitude_average_of_standardFrame (ℓ : ℕ)
    (hstandard : ∀ q : MvPolynomial (Fin 3) ℂ, q ∈ harmonicPolynomials ℓ →
      ∀ (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
      (∫ θ : ℝ, polynomialSphere q (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) =
        ((Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u : ℝ) *
          polynomialSphere q ⟨north, mem_sphere_zero_iff_norm.mpr north_norm⟩)
    (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ harmonicPolynomials ℓ)
    (g : Ambient ≃ₗᵢ[ℝ] Ambient) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (∫ θ : ℝ, polynomialSphere p (latitudePoint g u θ) ∂angleMeasure) =
        ((Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u : ℝ) *
          polynomialSphere p ⟨g north,
            mem_sphere_zero_iff_norm.mpr (by rw [g.norm_map, north_norm])⟩ := by
  have hh := hstandard (linearSubstitution (orthogonalSubstitutionMatrix g) p)
    (linearSubstitution_harmonic _ (orthogonalSubstitutionMatrix_orthogonal g) ℓ p hp) u hu
  simp_rw [orthogonalSubstitution_latitude] at hh
  simpa only [polynomialSphere, orthogonalSubstitution_eval] using hh

theorem harmonic_latitude_average (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) (g : Ambient ≃ₗᵢ[ℝ] Ambient)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (∫ θ : ℝ, polynomialSphere p (latitudePoint g u θ) ∂angleMeasure) =
      ((Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u : ℝ) *
        polynomialSphere p ⟨g north,
          mem_sphere_zero_iff_norm.mpr (by rw [g.norm_map, north_norm])⟩ := by
  apply harmonic_latitude_average_of_standardFrame ℓ _ p hp g u hu
  intro q hq v hv
  obtain ⟨Q, hprofile, hnorth⟩ := CircleAverage.latitude_average_polynomial q
  have hode := CircleAverage.latitude_average_legendre_ode ℓ q hq Q hprofile
  have hunique := DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke.CircleAverage.polynomial_shiftedLegendre_ode_unique ℓ Q hode
  rw [hprofile v hv, hunique, Polynomial.eval_mul, Polynomial.eval_C, hnorth]
  rw [Polynomial.eval_map]
  have hcast := Polynomial.hom_eval₂ (Polynomial.shiftedLegendre ℓ)
    (Int.castRingHom ℝ) Complex.ofRealHom v
  have hcomp : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := by
    ext n
    simp
  rw [hcomp] at hcast
  change (((Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) v : ℝ) : ℂ) =
    (Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℂ) (v : ℂ) at hcast
  rw [hcast, mul_comm]

private theorem uniform_projection (x : Sphere) :
    Measure.map (fun y : Sphere => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2)
      sphereArea = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  change Measure.map (fun y : Sphere => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2)
    (((volume : Measure Ambient).toSphere Set.univ)⁻¹ • (volume : Measure Ambient).toSphere) = _
  rw [ComplexFractionalInverse.KernelMass.normalized_area_projection_rotation 3 0 x]
  exact RawSphereProjection.normalized_coordinate_projection
instance instCompactSpaceFunkHeckeSphere : CompactSpace Sphere :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient) 1)
private theorem weighted_integrable (p : MvPolynomial (Fin 3) ℂ) (k : ℝ → ℝ)
    (hk : Integrable k (volume.restrict (Set.Icc (0 : ℝ) 1))) (x : Sphere) :
    Integrable (fun y : Sphere =>
      (k ((1 - inner ℝ (x : Ambient) (y : Ambient)) / 2) : ℂ) *
        polynomialSphere p y) sphereArea := by
  let φ : Sphere → ℝ := fun y => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2
  have hφ : Measurable φ := by dsimp [φ]; fun_prop
  have hkm : Integrable k (Measure.map φ sphereArea) := by
    rw [uniform_projection x]
    exact hk
  have hi : Integrable (fun y => (k (φ y) : ℂ)) sphereArea :=
    ((integrable_map_measure hkm.aestronglyMeasurable hφ.aemeasurable).mp hkm).ofReal
  have hp : Continuous (polynomialSphere p) := by
    unfold polynomialSphere
    induction p using MvPolynomial.induction_on with
    | C c => simpa using (continuous_const : Continuous (fun _ : Sphere => c))
    | add p q hp hq =>
      convert hp.add hq using 1 <;> ext y <;> simp
    | mul_X p i hp =>
      convert hp.mul (Complex.continuous_ofReal.comp
        ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val)) using 1
      ext y
      simp
  have h := (show IntegrableOn (fun y => (k (φ y) : ℂ)) Set.univ sphereArea by
    simpa using hi).mul_continuousOn hp.continuousOn isCompact_univ
  simpa [φ] using h

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral
open MeasureTheory ComplexFractionalInverse.RawSphereProjection

open scoped RealInnerProductSpace

theorem raw_polynomial_funkHecke (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) (w : ℝ → ℝ)
    (hw : Integrable w (volume.restrict (Set.Icc (0 : ℝ) 1))) (x : rawSphere) :
    (∫ y, rawLatitudeKernel w x p y ∂rawSphereArea) =
      ((∫ u : ℝ in Set.Icc 0 1,
        w u * (Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u : ℝ) : ℂ) *
        rawPolynomialSphere p x := by
  obtain ⟨g, hg⟩ := RawFiniteFunkHecke.exists_north_rotation x
  let F : rawSphere → ℂ := fun y =>
    (w ((1 - inner ℝ (x : rawAmbient) (y : rawAmbient)) / 2) : ℂ) * RawFiniteFunkHecke.polynomialSphere p y
  have hF : Integrable F rawSphereArea := RawFiniteFunkHecke.weighted_integrable p w hw x
  have hμ := RawFiniteFunkHecke.latitude_disintegration g
  have hprod := hμ.integrable_comp_of_integrable hF
  have hmap := integral_map hμ.measurable.aemeasurable
    (show AEStronglyMeasurable F (Measure.map
      (fun z : ℝ × ℝ => RawFiniteFunkHecke.latitudePoint g z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod RawFiniteFunkHecke.angleMeasure)) by
        rw [hμ.map_eq]
        exact hF.aestronglyMeasurable)
  rw [hμ.map_eq] at hmap
  change (∫ y, F y ∂rawSphereArea) = _
  rw [hmap]
  have hprod' : Integrable (fun z : ℝ × ℝ => F (RawFiniteFunkHecke.latitudePoint g z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod RawFiniteFunkHecke.angleMeasure) := hprod
  rw [integral_prod _ hprod']
  have hx : (⟨g RawFiniteFunkHecke.north,
      mem_sphere_zero_iff_norm.mpr (by rw [g.norm_map, RawFiniteFunkHecke.north_norm])⟩ : rawSphere) = x :=
    Subtype.ext hg
  calc
    _ = ∫ u : ℝ in Set.Icc 0 1,
        (w u : ℂ) *
          ((Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u : ℝ) *
            RawFiniteFunkHecke.polynomialSphere p x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      change (∫ θ : ℝ, F (RawFiniteFunkHecke.latitudePoint g u θ) ∂RawFiniteFunkHecke.angleMeasure) = _
      have hpoint (θ : ℝ) : F (RawFiniteFunkHecke.latitudePoint g u θ) =
          (w u : ℂ) * RawFiniteFunkHecke.polynomialSphere p (RawFiniteFunkHecke.latitudePoint g u θ) := by
        dsimp [F, rawLatitudeKernel]
        rw [RawFiniteFunkHecke.latitudePoint_projection x g hg u θ hu]
      simp_rw [hpoint]
      rw [integral_const_mul, RawFiniteFunkHecke.harmonic_latitude_average ℓ p hp g u hu, hx]
      ring
    _ = _ := by
      rw [integral_mul_const]
      congr 1
      simp_rw [← Complex.ofReal_mul]
      exact integral_complex_ofReal
end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral
