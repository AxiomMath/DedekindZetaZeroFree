module

public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.FractionalIntegrals.NormalizedKernel

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke
open MeasureTheory
open scoped RealInnerProductSpace BoundedContinuousFunction

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

end DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke
