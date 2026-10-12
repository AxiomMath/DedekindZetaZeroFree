module

public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import DedekindZetaZeroFree.MeasureTheory.Sphere.EuclideanAreaNormalization
public import DedekindZetaZeroFree.Metaplectic.Kubota.ComplexCharactersHaarAndSU2Splitting
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

@[expose] public section

namespace DedekindZetaZeroFree.ComplexLocal.StereographicTransport.RawCone
open MeasureTheory Set
open scoped Pointwise ENNReal
open ComplexFractionalInverse.RawSphereProjection
open KPCplxCharacterHaar

noncomputable def denominator (z : ℂ) : ℝ := 1 + ‖z‖ ^ 2

private theorem denominator_pos (z : ℂ) : 0 < denominator z := by
  unfold denominator
  positivity

noncomputable def sigmaVector (z : ℂ) : rawAmbient :=
  WithLp.toLp 2 ![2 * z.re / denominator z, -2 * z.im / denominator z,
    (1 - ‖z‖ ^ 2) / denominator z]

theorem sigmaVector_norm (z : ℂ) : ‖sigmaVector z‖ = 1 := by
  have hn : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    simpa only [Complex.normSq_apply, ← sq] using (Complex.normSq_eq_norm_sq z)
  have hD := (denominator_pos z).ne'
  have hs : ‖sigmaVector z‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [sigmaVector, Fin.sum_univ_three, PiLp.toLp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    change (2 * z.re / denominator z)^2 + (-2 * z.im / denominator z)^2 +
      ((1 - ‖z‖^2) / denominator z)^2 = 1
    dsimp [denominator] at *
    field_simp
    nlinarith
  nlinarith [norm_nonneg (sigmaVector z)]

noncomputable def sigma (z : ℂ) : rawSphere :=
  ⟨sigmaVector z, mem_sphere_zero_iff_norm.mpr (sigmaVector_norm z)⟩

noncomputable def planeProbability : Measure ℂ :=
  euclideanArea.withDensity
    (fun z => ENNReal.ofReal (denominator z ^ (-2 : ℝ) / Real.pi))

theorem sigma_continuous : Continuous sigma := by
  apply Continuous.subtype_mk
  unfold sigmaVector
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  all_goals dsimp [denominator]
  all_goals fun_prop (disch := intro z; positivity)

noncomputable def invChart (y : rawSphere) : ℂ :=
  ⟨(y : rawAmbient) 0 / (1 + (y : rawAmbient) 2),
    -(y : rawAmbient) 1 / (1 + (y : rawAmbient) 2)⟩
theorem sigma_height (z : ℂ) : (1 + (sigma z : rawAmbient) 2) = 2 / denominator z := by
  change 1 + (1 - ‖z‖ ^ 2) / denominator z = _
  unfold denominator
  have : (1 + ‖z‖ ^ 2) ≠ 0 := by positivity
  field_simp
  <;> ring
theorem invChart_left (z : ℂ) : Complex.mk
    ((sigma z : rawAmbient) 0 / (1 + (sigma z : rawAmbient) 2))
    (-(sigma z : rawAmbient) 1 / (1 + (sigma z : rawAmbient) 2)) = z := by
  rw [sigma_height]
  apply Complex.ext
  · change (2 * z.re / denominator z) / (2 / denominator z) = z.re
    have : denominator z ≠ 0 := by unfold denominator; positivity
    field_simp
  · change -(-2 * z.im / denominator z) / (2 / denominator z) = z.im
    have : denominator z ≠ 0 := by unfold denominator; positivity
    field_simp

theorem invChart_norm (y : rawSphere) (hy : (y : rawAmbient) 2 ≠ -1) :
    ‖invChart y‖ ^ 2 = (1 - (y : rawAmbient) 2) / (1 + (y : rawAmbient) 2) := by
  have hN : (y : rawAmbient) 0 ^ 2 + (y : rawAmbient) 1 ^ 2 +
      (y : rawAmbient) 2 ^ 2 = 1 := by
    have h := mem_sphere_zero_iff_norm.mp y.property
    have h2 := EuclideanSpace.real_norm_sq_eq (y : rawAmbient)
    rw [h] at h2
    simpa [Fin.sum_univ_three] using h2.symm
  have hn := Complex.normSq_eq_norm_sq (invChart y)
  simp only [Complex.normSq_apply] at hn
  have hD : 1 + (y : rawAmbient) 2 ≠ 0 := by intro h; apply hy; linarith
  rw [← hn]
  dsimp [invChart]
  field_simp
  nlinarith
theorem invChart_denominator (y : rawSphere) (hy : (y : rawAmbient) 2 ≠ -1) :
    denominator (invChart y) = 2 / (1 + (y : rawAmbient) 2) := by
  unfold denominator
  rw [invChart_norm y hy]
  have hD : 1 + (y : rawAmbient) 2 ≠ 0 := by intro h; apply hy; linarith
  field_simp
  ring
theorem invChart_right (y : rawSphere) (hy : (y : rawAmbient) 2 ≠ -1) : sigma (invChart y) = y := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  all_goals change sigmaVector (invChart y) _ = _
  all_goals simp only [sigmaVector, PiLp.toLp_apply, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · rw [invChart_denominator y hy]
    change 2 * ((y : rawAmbient) 0 / (1 + (y : rawAmbient) 2)) /
      (2 / (1 + (y : rawAmbient) 2)) = _
    have hD : 1 + (y : rawAmbient) 2 ≠ 0 := by intro h; apply hy; linarith
    field_simp
    rfl
  · rw [invChart_denominator y hy]
    change -2 * (-(y : rawAmbient) 1 / (1 + (y : rawAmbient) 2)) /
      (2 / (1 + (y : rawAmbient) 2)) = _
    have hD : 1 + (y : rawAmbient) 2 ≠ 0 := by intro h; apply hy; linarith
    field_simp
    rfl
  · change (1 - ‖invChart y‖ ^ 2) / denominator (invChart y) = (y : rawAmbient) 2
    rw [invChart_denominator y hy, invChart_norm y hy]
    have hD : 1 + (y : rawAmbient) 2 ≠ 0 := by intro h; apply hy; linarith
    field_simp
    ring

theorem sigma_injective : Function.Injective sigma := by
  intro z w h
  have he := congrArg invChart h
  simpa only [invChart, invChart_left] using he

noncomputable def cone (q : ℝ × ℂ) : rawAmbient := q.1 • sigmaVector q.2

theorem cone_injective : Set.InjOn cone (Ioo 0 1 ×ˢ (univ : Set ℂ)) := by
  rintro ⟨t,z⟩ ⟨ht,hz⟩ ⟨r,w⟩ ⟨hr,hw⟩ he
  change t • sigmaVector z = r • sigmaVector w at he
  have heNorm := congrArg norm he
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1, abs_of_pos hr.1,
    sigmaVector_norm, mul_one] at heNorm
  have he' : sigmaVector z = sigmaVector w := by
    rw [heNorm] at he
    have hh := congrArg (fun v : rawAmbient => r⁻¹ • v) he
    simpa only [smul_smul, inv_mul_cancel₀ (show r ≠ 0 from hr.1.ne'), one_smul] using hh
  exact Prod.ext heNorm (sigma_injective (Subtype.ext he'))

theorem south_ray_null : (volume : Measure rawAmbient)
    {v : rawAmbient | v 0 = 0 ∧ v 1 = 0 ∧ v 2 ≤ 0} = 0 := by
  apply measure_mono_null (fun x hx => hx.1)
  let l : rawAmbient →ₗ[ℝ] ℝ :=
    (LinearMap.proj (0 : Fin 3)).comp (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap
  have hker : l.ker ≠ ⊤ := by
    intro h
    have hv : WithLp.toLp 2 ![(1 : ℝ), 0, 0] ∈ l.ker := by rw [h]; trivial
    change (1 : ℝ) = 0 at hv
    norm_num at hv
  exact Measure.addHaar_submodule volume l.ker hker

namespace CV

noncomputable def D (v : rawAmbient) : ℝ := 1 + v 1 ^ 2 + v 2 ^ 2
noncomputable def coneR (v : rawAmbient) : rawAmbient :=
  WithLp.toLp 2 ![2 * v 0 * v 1 / D v, -2 * v 0 * v 2 / D v,
    v 0 * (1-v 1 ^ 2-v 2 ^ 2) / D v]
lemma D_pos (v : rawAmbient) : 0 < D v := by dsimp [D]; positivity

noncomputable def jac (v : rawAmbient) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2*v 1 / D v, 2*v 0 / D v - 4*v 0*v 1^2/(D v)^2, -4*v 0*v 1*v 2/(D v)^2;
    -2*v 2 / D v, 4*v 0*v 1*v 2/(D v)^2, -2*v 0 / D v + 4*v 0*v 2^2/(D v)^2;
    (1-v 1^2-v 2^2)/D v, -4*v 0*v 1/(D v)^2, -4*v 0*v 2/(D v)^2]

lemma jac_det (v : rawAmbient) : (jac v).det = -4*v 0^2/(D v)^2 := by
  rw [Matrix.det_fin_three]
  simp [jac, D, Matrix.cons_val, Matrix.vecHead, Matrix.vecTail]
  have hd := (D_pos v).ne'
  dsimp [D] at hd
  field_simp
  ring

lemma cone_deriv (v : rawAmbient) :
    HasFDerivAt coneR ((jac v).toEuclideanLin.toContinuousLinearMap) v := by
  rw [← hasFDerivWithinAt_univ]
  apply (hasFDerivWithinAt_piLp 2).mpr
  intro i
  have h0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 v (0 : Fin 3)
  have h1 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 v (1 : Fin 3)
  have h2 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 v (2 : Fin 3)
  have hD := ((hasFDerivAt_const (1 : ℝ) v).add (h1.pow 2)).add (h2.pow 2)
  have hI := (hasFDerivAt_inv (D_pos v).ne').comp v hD
  fin_cases i
  · have h := (((h0.const_mul 2).mul h1).mul hI)
    rw [hasFDerivWithinAt_univ]
    simp only [coneR, PiLp.toLp_apply, Matrix.cons_val, Matrix.vecHead, Matrix.vecTail]
    simp_rw [div_eq_mul_inv]
    apply h.congr_fderiv
    ext w
    simp [jac, Matrix.toEuclideanLin, Matrix.toLpLin_apply, PiLp.proj_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val, Matrix.vecHead, Matrix.vecTail, D]
    ring
  · have h := (((h0.const_mul (-2)).mul h2).mul hI)
    rw [hasFDerivWithinAt_univ]
    simp only [coneR, PiLp.toLp_apply, Matrix.cons_val, Matrix.vecHead, Matrix.vecTail]
    simp_rw [div_eq_mul_inv]
    apply h.congr_fderiv
    ext w
    simp [jac, Matrix.toEuclideanLin, Matrix.toLpLin_apply, PiLp.proj_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val, Matrix.vecHead, Matrix.vecTail, D]
    ring
  · have h := ((h0.mul (((hasFDerivAt_const (1 : ℝ) v).sub (h1.pow 2)).sub (h2.pow 2))).mul hI)
    rw [hasFDerivWithinAt_univ]
    simp only [coneR, PiLp.toLp_apply, Matrix.cons_val, Matrix.vecHead, Matrix.vecTail]
    simp_rw [div_eq_mul_inv]
    apply h.congr_fderiv
    ext w
    simp [jac, Matrix.toEuclideanLin, Matrix.toLpLin_apply, PiLp.proj_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val, Matrix.vecHead, Matrix.vecTail, D]
    field_simp
    ring
lemma abs_det (v : rawAmbient) : |((jac v).toEuclideanLin.toContinuousLinearMap).det| =
    4 * v 0 ^ 2 / D v ^ 2 := by
  change |LinearMap.det ((jac v).toEuclideanLin)| = _
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, jac_det]
  rw [show -4 * v 0 ^ 2 / D v ^ 2 = -(4 * v 0 ^ 2 / D v ^ 2) by ring,
    abs_neg, abs_of_nonneg (by positivity)]

noncomputable def coords : rawAmbient ≃ᵐ ℝ × ℂ :=
  split.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
    ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans Complex.measurableEquivPi.symm))
lemma coords_mp : MeasurePreserving coords volume (volume.prod euclideanArea) := by
  exact split_preserving.trans ((MeasurePreserving.id volume).prod
    ((PiLp.volume_preserving_ofLp (Fin 2)).trans Complex.volume_preserving_equiv_pi.symm))
lemma coords_symm (q : ℝ × ℂ) : coords.symm q = WithLp.toLp 2 ![q.1, q.2.re, q.2.im] := by
  rw [coords, MeasurableEquiv.trans_symm, MeasurableEquiv.trans_apply, split_symm_apply]
  ext i
  fin_cases i <;> rfl
lemma coords_D (q : ℝ × ℂ) : D (coords.symm q) = denominator q.2 := by
  rw [coords_symm]
  dsimp [D, denominator]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring
lemma coords_cone (q : ℝ × ℂ) : coneR (coords.symm q) = cone q := by
  rw [coords_symm]
  ext i
  have hn := Complex.normSq_eq_norm_sq q.2
  simp only [Complex.normSq_apply] at hn
  fin_cases i <;> dsimp [coneR, cone, sigmaVector, D, denominator]
  all_goals rw [← hn]; field_simp; ring
lemma cone_image_ae (s : Set rawSphere) :
    cone '' (Ioo (0 : ℝ) 1 ×ˢ (sigma ⁻¹' s)) =ᵐ[volume]
      Ioo (0 : ℝ) 1 • (Subtype.val '' s) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp south_ray_null] with v hv
  apply propext
  constructor
  · rintro ⟨⟨t,z⟩, ⟨ht,hz⟩, rfl⟩
    exact ⟨t, ht, sigmaVector z, ⟨sigma z, hz, rfl⟩, rfl⟩
  · rintro ⟨t, ht, w, ⟨y, hy, rfl⟩, rfl⟩
    have hys : (y : rawAmbient) 2 ≠ -1 := by
      intro he
      apply hv
      have hn := EuclideanSpace.real_norm_sq_eq (y : rawAmbient)
      have hn1 := mem_sphere_zero_iff_norm.mp y.property
      rw [hn1] at hn
      simp [Fin.sum_univ_three, he] at hn
      have h0 : (y : rawAmbient) 0 = 0 := by nlinarith [sq_nonneg ((y : rawAmbient) 1)]
      have h1 : (y : rawAmbient) 1 = 0 := by nlinarith [sq_nonneg ((y : rawAmbient) 0)]
      change t * (y : rawAmbient) 0 = 0 ∧ t * (y : rawAmbient) 1 = 0 ∧
        t * (y : rawAmbient) 2 ≤ 0
      simp [h0, h1, he, ht.1.le]
    refine ⟨(t, invChart y), ⟨ht, ?_⟩, ?_⟩
    · simpa only [mem_preimage, invChart_right y hys] using hy
    · change t • (sigma (invChart y) : rawAmbient) = _
      rw [invChart_right y hys]

lemma coneR_image_ae (s : Set rawSphere) :
    coneR '' (coords ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ (sigma ⁻¹' s))) =ᵐ[volume]
      Ioo (0 : ℝ) 1 • (Subtype.val '' s) := by
  have he : coneR '' (coords ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ (sigma ⁻¹' s))) =
      cone '' (Ioo (0 : ℝ) 1 ×ˢ (sigma ⁻¹' s)) := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨coords x, hx, ?_⟩
      rw [← coords_cone, coords.symm_apply_apply]
    · rintro ⟨q, hq, rfl⟩
      refine ⟨coords.symm q, by simpa, coords_cone q⟩
  rw [he]
  exact cone_image_ae s

lemma radial_integral : (∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ 2)) =
    ENNReal.ofReal (1 / 3 : ℝ) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((Continuous.integrableOn_Icc (f := fun t : ℝ => t ^ 2) (by fun_prop)).mono_set Ioo_subset_Icc_self)]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
    norm_num
  · exact Filter.Eventually.of_forall (fun t => sq_nonneg t)

lemma jac_integral (s : Set rawSphere) (hs : MeasurableSet s) :
    (∫⁻ v in coords ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ (sigma ⁻¹' s)),
      ENNReal.ofReal (4 * v 0 ^ 2 / D v ^ 2)) =
    ENNReal.ofReal (4 / 3 : ℝ) *
      ∫⁻ z in sigma ⁻¹' s, ENNReal.ofReal (denominator z ^ (-2 : ℝ)) ∂euclideanArea := by
  letI : SFinite euclideanArea := by change SFinite (volume : Measure ℂ); infer_instance
  have hsm := sigma_continuous.measurable hs
  have hm : Measurable (fun q : ℝ × ℂ => ENNReal.ofReal (4 * q.1 ^ 2 / denominator q.2 ^ 2)) := by
    dsimp [denominator]; fun_prop
  have hp := coords_mp.setLIntegral_comp_preimage (s := Ioo (0 : ℝ) 1 ×ˢ (sigma ⁻¹' s))
    (measurableSet_Ioo.prod hsm) hm
  have he : (fun v : rawAmbient => ENNReal.ofReal (4 * v 0 ^ 2 / D v ^ 2)) =
      (fun v => ENNReal.ofReal (4 * (coords v).1 ^ 2 / denominator (coords v).2 ^ 2)) := by
    ext v
    have hd := coords_D (coords v)
    have ht := coords_symm (coords v)
    simp only [coords.symm_apply_apply] at hd ht
    have ht0 := congrArg (fun w : rawAmbient => w 0) ht
    simp only [PiLp.toLp_apply, Matrix.cons_val_zero] at ht0
    rw [hd, ht0]
  rw [he, hp, setLIntegral_prod _ hm.aemeasurable.restrict]
  have hg : ∀ z : ℂ, denominator z ^ (-2 : ℝ) = (denominator z ^ 2)⁻¹ := by
    intro z
    rw [Real.rpow_neg (by dsimp [denominator]; positivity), Real.rpow_two]
  simp_rw [hg, div_eq_mul_inv,
    ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg _)),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hf : Measurable (fun z : ℂ => ENNReal.ofReal (denominator z ^ 2)⁻¹) := by
    dsimp [denominator]; fun_prop
  simp_rw [lintegral_const_mul _ hf]
  rw [lintegral_mul_const _ (by fun_prop)]
  rw [lintegral_const_mul _ (by fun_prop), radial_integral]
  congr 1 <;> norm_num

end CV

theorem cone_volume_stereographic (s : Set rawSphere) (hs : MeasurableSet s) :
    (volume : Measure rawAmbient) (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) =
      ENNReal.ofReal (4 / 3 : ℝ) *
      ∫⁻ z in sigma ⁻¹' s, ENNReal.ofReal (denominator z ^ (-2 : ℝ)) ∂euclideanArea := by
  let S := CV.coords ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ (sigma ⁻¹' s))
  have hm : MeasurableSet S := CV.coords.measurable
    (measurableSet_Ioo.prod (sigma_continuous.measurable hs))
  have hi : InjOn CV.coneR S := by
    intro x hx y hy he
    apply CV.coords.injective
    apply cone_injective
      (show CV.coords x ∈ Ioo 0 1 ×ˢ (univ : Set ℂ) from ⟨hx.1, mem_univ _⟩)
      (show CV.coords y ∈ Ioo 0 1 ×ˢ (univ : Set ℂ) from ⟨hy.1, mem_univ _⟩)
    simpa only [← CV.coords_cone, CV.coords.symm_apply_apply] using he
  rw [← measure_congr (CV.coneR_image_ae s), ← lintegral_abs_det_fderiv_eq_addHaar_image
    volume hm (fun x hx => (CV.cone_deriv x).hasFDerivWithinAt) hi]
  simp_rw [CV.abs_det]
  exact CV.jac_integral s hs

end DedekindZetaZeroFree.ComplexLocal.StereographicTransport.RawCone
