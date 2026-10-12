module

public import DedekindZetaZeroFree.MeasureTheory.SphereCoordinateDistribution

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse

open MeasureTheory
open Set
open scoped Pointwise RealInnerProductSpace ENNReal

noncomputable def sphereRotation (g : Ambient ≃ₗᵢ[ℝ] Ambient) (x : Sphere) : Sphere :=
  ⟨g x, by simpa only [mem_sphere_zero_iff_norm, g.norm_map] using x.property⟩
lemma sphereRotation_continuous (g : Ambient ≃ₗᵢ[ℝ] Ambient) :
    Continuous (sphereRotation g) := by
  exact (g.continuous.comp continuous_subtype_val).subtype_mk _
lemma sphereRotation_cone_preimage (g : Ambient ≃ₗᵢ[ℝ] Ambient) (s : Set Sphere) :
    g ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) =
    Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereRotation g ⁻¹' s)) := by
  ext z
  constructor
  · rintro ⟨r, hr, w, ⟨y, hy, rfl⟩, hz⟩
    refine ⟨r, hr, g.symm y, ⟨sphereRotation g.symm y, ?_, rfl⟩, ?_⟩
    · simpa [sphereRotation] using hy
    · have := congrArg g.symm hz
      simpa using this
  · rintro ⟨r, hr, w, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨r, hr, g y, ⟨sphereRotation g y, hy, rfl⟩, by simp⟩
lemma sphereRotation_preserving (g : Ambient ≃ₗᵢ[ℝ] Ambient) :
    MeasurePreserving (sphereRotation g) (volume : Measure Ambient).toSphere
      (volume : Measure Ambient).toSphere := by
  refine ⟨(sphereRotation_continuous g).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereRotation_continuous g).measurable hs,
    Measure.toSphere_apply' _ ((sphereRotation_continuous g).measurable hs),
    Measure.toSphere_apply' _ hs, ← sphereRotation_cone_preimage]
  rw [g.measurePreserving.measure_preimage_emb g.toHomeomorph.measurableEmbedding]
lemma sphereArea_rotation_preserving (g : Ambient ≃ₗᵢ[ℝ] Ambient) :
    MeasurePreserving (sphereRotation g) sphereArea sphereArea := by
  exact (sphereRotation_preserving g).smul_measure _
lemma sphereArea_projection_rotation (g : Ambient ≃ₗᵢ[ℝ] Ambient) (x : Sphere) :
    Measure.map (fun y : Sphere => (1 - inner ℝ (g x) (y : Ambient)) / 2) sphereArea =
    Measure.map (fun y : Sphere => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2) sphereArea := by
  have hp : Measurable (fun y : Sphere => (1 - inner ℝ (g x) (y : Ambient)) / 2) := by fun_prop
  calc
    _ = Measure.map (fun y : Sphere => (1 - inner ℝ (g x) (y : Ambient)) / 2)
        (Measure.map (sphereRotation g) sphereArea) := by
          rw [(sphereArea_rotation_preserving g).map_eq]
    _ = _ := by
      rw [Measure.map_map hp (sphereRotation_continuous g).measurable]
      congr 1
      ext y
      simp [Function.comp_def, sphereRotation, g.inner_map_map]
lemma sphereArea_projection_independent (x z : Sphere) :
    Measure.map (fun y : Sphere => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2) sphereArea =
    Measure.map (fun y : Sphere => (1 - inner ℝ (z : Ambient) (y : Ambient)) / 2) sphereArea := by
  let g := (ℝ ∙ ((z : Ambient) - (x : Ambient)))ᗮ.reflection
  have hg : g z = (x : Ambient) := Submodule.reflection_sub (by
    rw [mem_sphere_zero_iff_norm.mp z.property, mem_sphere_zero_iff_norm.mp x.property])
  simpa [hg] using sphereArea_projection_rotation g z

lemma sphereProjection_raw_mass :
    (volume : Measure Ambient).toSphere univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [Measure.toSphere_apply_univ, EuclideanSpace.volume_ball_fin_three]
  have hd : Module.finrank ℝ Ambient = 3 := by simp [Ambient]
  simp only [hd, Nat.cast_ofNat, ENNReal.ofReal_one, one_pow, one_mul]
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

noncomputable def sphereProjection_split : Ambient ≃ᵐ ℝ × EuclideanSpace ℝ (Fin 2) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm |>.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))
lemma sphereProjection_split_preserving : MeasurePreserving sphereProjection_split := by
  exact (PiLp.volume_preserving_ofLp (Fin 3)).trans
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))))
lemma sphereProjection_split_symm_apply (z : ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    sphereProjection_split.symm (z,w) = WithLp.toLp 2 (Fin.cons z w.ofLp) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [sphereProjection_split, MeasurableEquiv.prodCongr] <;> rfl
lemma sphereProjection_split_norm_sq (z : ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    ‖sphereProjection_split.symm (z,w)‖ ^ 2 = z ^ 2 + ‖w‖ ^ 2 := by
  rw [sphereProjection_split_symm_apply]
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]

lemma sphereProjection_north_cone (t : ℝ) (i : Fin 3) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' {y : Sphere | t ≤ (y : Ambient) i}) =
      {v : Ambient | 0 < ‖v‖ ∧ ‖v‖ < 1 ∧ t * ‖v‖ ≤ v i} := by
  ext v
  constructor
  · rintro ⟨r, hr, _, ⟨y, hy, rfl⟩, rfl⟩
    have hn : ‖r • (y : Ambient)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1,
        mem_sphere_zero_iff_norm.mp y.property, mul_one]
    simp only [mem_setOf_eq, hn]
    refine ⟨hr.1, hr.2, ?_⟩
    change t * r ≤ r * (y : Ambient) i
    simpa only [mul_comm t r] using mul_le_mul_of_nonneg_left hy hr.1.le
  · rintro ⟨hp, hlt, hi⟩
    let y : Sphere := ⟨‖v‖⁻¹ • v, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']⟩
    refine ⟨‖v‖, ⟨hp, hlt⟩, y, ⟨y, ?_, rfl⟩, ?_⟩
    · change t ≤ ‖v‖⁻¹ * v i
      exact (le_inv_mul_iff₀ hp).mpr (by simpa only [mul_comm] using hi)
    · simp [y, smul_smul, hp.ne']
lemma sphereProjection_north_cone_Fubini (t : ℝ) :
    volume (Ioo (0 : ℝ) 1 • (Subtype.val '' {y : Sphere | t ≤ (y : Ambient) 0})) =
      ∫⁻ z : ℝ, volume {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖sphereProjection_split.symm (z,w)‖ ∧
        ‖sphereProjection_split.symm (z,w)‖ < 1 ∧
        t * ‖sphereProjection_split.symm (z,w)‖ ≤ z} := by
  rw [sphereProjection_north_cone]
  have hm : MeasurableSet {v : Ambient | 0 < ‖v‖ ∧ ‖v‖ < 1 ∧ t * ‖v‖ ≤ v 0} := by
    measurability
  rw [← sphereProjection_split_preserving.symm.measure_preimage hm.nullMeasurableSet]
  rw [Measure.volume_eq_prod, Measure.prod_apply (sphereProjection_split.symm.measurable hm)]
  congr 1
lemma sphereProjection_north_slice_lower {t z : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hz : 0 < z) (hzt : z < t) :
    {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖sphereProjection_split.symm (z,w)‖ ∧
        ‖sphereProjection_split.symm (z,w)‖ < 1 ∧
        t * ‖sphereProjection_split.symm (z,w)‖ ≤ z} =
      Metric.closedBall 0 (Real.sqrt ((z / t) ^ 2 - z ^ 2)) := by
  have hpos : 0 ≤ (z / t) ^ 2 - z ^ 2 := by
    have h : z ≤ z / t := (le_div_iff₀ ht).mpr (by nlinarith)
    nlinarith [div_pos hz ht]
  ext w
  have hn := sphereProjection_split_norm_sq z w
  have hn0 := norm_nonneg (sphereProjection_split.symm (z,w))
  have hw0 := norm_nonneg w
  have hs := Real.sq_sqrt hpos
  have hzdiv := div_pos hz ht
  have hdiv : z / t < 1 := (div_lt_one ht).mpr hzt
  rw [Metric.mem_closedBall, dist_zero_right]
  simp only [mem_setOf_eq]
  constructor
  · rintro ⟨_, _, hc⟩
    have hc' : ‖sphereProjection_split.symm (z,w)‖ ≤ z / t :=
      (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hc)
    have : ‖w‖ ^ 2 ≤ (Real.sqrt ((z / t) ^ 2 - z ^ 2)) ^ 2 := by
      nlinarith
    exact (sq_le_sq₀ hw0 (Real.sqrt_nonneg _)).mp this
  · intro hw
    have hwsq : ‖w‖ ^ 2 ≤ (Real.sqrt ((z / t) ^ 2 - z ^ 2)) ^ 2 :=
      (sq_le_sq₀ hw0 (Real.sqrt_nonneg _)).mpr hw
    have hnle : ‖sphereProjection_split.symm (z,w)‖ ≤ z / t := by
      apply (sq_le_sq₀ hn0 hzdiv.le).mp
      nlinarith
    refine ⟨?_, lt_of_le_of_lt hnle hdiv, ?_⟩
    · nlinarith [sq_pos_of_pos hz]
    · have := (le_div_iff₀ ht).mp hnle
      simpa only [mul_comm] using this
lemma sphereProjection_north_slice_upper {t z : ℝ} (ht : 0 < t) (htz : t ≤ z)
    (hz1 : z < 1) :
    {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖sphereProjection_split.symm (z,w)‖ ∧
        ‖sphereProjection_split.symm (z,w)‖ < 1 ∧
        t * ‖sphereProjection_split.symm (z,w)‖ ≤ z} =
      Metric.ball 0 (Real.sqrt (1 - z ^ 2)) := by
  have hz : 0 < z := lt_of_lt_of_le ht htz
  have hpos : 0 < 1 - z ^ 2 := by nlinarith
  ext w
  have hn := sphereProjection_split_norm_sq z w
  have hn0 := norm_nonneg (sphereProjection_split.symm (z,w))
  have hw0 := norm_nonneg w
  have hs := Real.sq_sqrt hpos.le
  rw [Metric.mem_ball, dist_zero_right]
  simp only [mem_setOf_eq]
  constructor
  · rintro ⟨_, hnlt, _⟩
    apply (sq_lt_sq₀ hw0 (Real.sqrt_nonneg _)).mp
    nlinarith
  · intro hw
    have hwsq := (sq_lt_sq₀ hw0 (Real.sqrt_nonneg _)).mpr hw
    have hnlt : ‖sphereProjection_split.symm (z,w)‖ < 1 := by nlinarith
    refine ⟨?_, hnlt, ?_⟩
    · nlinarith [sq_pos_of_pos hz]
    · calc
        _ ≤ t * 1 := mul_le_mul_of_nonneg_left hnlt.le ht.le
        _ ≤ z := by simpa using htz
lemma sphereProjection_north_slice_empty {t z : ℝ} (ht : 0 < t)
    (hz : z ≤ 0 ∨ 1 ≤ z) :
    {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖sphereProjection_split.symm (z,w)‖ ∧
        ‖sphereProjection_split.symm (z,w)‖ < 1 ∧
        t * ‖sphereProjection_split.symm (z,w)‖ ≤ z} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro w
  rintro ⟨hnpos, hnlt, hc⟩
  have hn := sphereProjection_split_norm_sq z w
  have hw := sq_nonneg ‖w‖
  have hn0 := norm_nonneg (sphereProjection_split.symm (z,w))
  rcases hz with hz | hz
  · nlinarith
  · nlinarith
lemma sphereProjection_north_slice_volume_lower {t z : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hz : 0 < z) (hzt : z < t) :
    volume {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖sphereProjection_split.symm (z,w)‖ ∧
        ‖sphereProjection_split.symm (z,w)‖ < 1 ∧
        t * ‖sphereProjection_split.symm (z,w)‖ ≤ z} =
      ENNReal.ofReal (Real.pi * ((z / t) ^ 2 - z ^ 2)) := by
  rw [sphereProjection_north_slice_lower ht ht1 hz hzt, EuclideanSpace.volume_closedBall_fin_two]
  have hpos : 0 ≤ (z / t) ^ 2 - z ^ 2 := by
    have h : z ≤ z / t := (le_div_iff₀ ht).mpr (by nlinarith)
    nlinarith [div_pos hz ht]
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hpos,
    ← ENNReal.ofReal_mul hpos, mul_comm]
lemma sphereProjection_north_slice_volume_upper {t z : ℝ} (ht : 0 < t) (htz : t ≤ z)
    (hz1 : z < 1) :
    volume {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖sphereProjection_split.symm (z,w)‖ ∧
        ‖sphereProjection_split.symm (z,w)‖ < 1 ∧
        t * ‖sphereProjection_split.symm (z,w)‖ ≤ z} =
      ENNReal.ofReal (Real.pi * (1 - z ^ 2)) := by
  rw [sphereProjection_north_slice_upper ht htz hz1, EuclideanSpace.volume_ball_fin_two]
  have hz : 0 < z := lt_of_lt_of_le ht htz
  have hpos : 0 ≤ 1 - z ^ 2 := by nlinarith
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hpos,
    ← ENNReal.ofReal_mul hpos, mul_comm]

lemma sphereProjection_north_cone_integrals {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    volume (Ioo (0 : ℝ) 1 • (Subtype.val '' {y : Sphere | t ≤ (y : Ambient) 0})) =
      (∫⁻ z in Ioo 0 t, ENNReal.ofReal (Real.pi * ((z / t) ^ 2 - z ^ 2))) +
      (∫⁻ z in Ico t 1, ENNReal.ofReal (Real.pi * (1 - z ^ 2))) := by
  rw [sphereProjection_north_cone_Fubini]
  have heq : (fun z : ℝ => volume {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖sphereProjection_split.symm (z,w)‖ ∧
        ‖sphereProjection_split.symm (z,w)‖ < 1 ∧
        t * ‖sphereProjection_split.symm (z,w)‖ ≤ z}) =
      (Ioo 0 t).indicator (fun z => ENNReal.ofReal (Real.pi * ((z / t) ^ 2 - z ^ 2))) +
      (Ico t 1).indicator (fun z => ENNReal.ofReal (Real.pi * (1 - z ^ 2))) := by
    ext z
    by_cases hz : 0 < z
    · by_cases hzt : z < t
      · simp only [Pi.add_apply, indicator_of_mem (show z ∈ Ioo 0 t from ⟨hz,hzt⟩)]
        rw [sphereProjection_north_slice_volume_lower ht ht1 hz hzt,
          indicator_of_notMem (show z ∉ Ico t 1 from fun h => (not_le.mpr hzt) h.1), add_zero]
      · by_cases hz1 : z < 1
        · rw [sphereProjection_north_slice_volume_upper ht (le_of_not_gt hzt) hz1]
          simp [indicator_of_notMem (show z ∉ Ioo 0 t from fun h => hzt h.2),
            indicator_of_mem (show z ∈ Ico t 1 from ⟨le_of_not_gt hzt,hz1⟩)]
        · rw [sphereProjection_north_slice_empty ht (Or.inr (le_of_not_gt hz1))]
          simp [indicator_of_notMem (show z ∉ Ioo 0 t from fun h => hzt h.2),
            indicator_of_notMem (show z ∉ Ico t 1 from fun h => hz1 h.2)]
    · rw [sphereProjection_north_slice_empty ht (Or.inl (le_of_not_gt hz))]
      simp [indicator_of_notMem (show z ∉ Ioo 0 t from fun h => hz h.1),
        indicator_of_notMem (show z ∉ Ico t 1 from fun h => hz (lt_of_lt_of_le ht h.1))]
  rw [heq]
  change (∫⁻ z, (Ioo 0 t).indicator (fun z => ENNReal.ofReal (Real.pi * ((z / t) ^ 2 - z ^ 2))) z +
    (Ico t 1).indicator (fun z => ENNReal.ofReal (Real.pi * (1 - z ^ 2))) z) = _
  rw [lintegral_add_left
    ((Measurable.ennreal_ofReal (by fun_prop)).indicator measurableSet_Ioo)
    ((Ico t 1).indicator _), lintegral_indicator measurableSet_Ioo,
    lintegral_indicator measurableSet_Ico]
lemma sphereProjection_north_cone_volume {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    volume (Ioo (0 : ℝ) 1 • (Subtype.val '' {y : Sphere | t ≤ (y : Ambient) 0})) =
      ENNReal.ofReal (2 * Real.pi / 3 * (1 - t)) := by
  rw [sphereProjection_north_cone_integrals ht ht1]
  have hlint : IntegrableOn (fun z : ℝ => Real.pi * ((z / t) ^ 2 - z ^ 2)) (Ioo 0 t) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
  have huint : IntegrableOn (fun z : ℝ => Real.pi * (1 - z ^ 2)) (Ico t 1) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ico_subset_Icc_self
  have hln : 0 ≤ᵐ[volume.restrict (Ioo 0 t)] (fun z : ℝ => Real.pi * ((z / t) ^ 2 - z ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    apply mul_nonneg Real.pi_pos.le
    have h : z ≤ z / t := (le_div_iff₀ ht).mpr (by nlinarith [hz.1,hz.2])
    exact sub_nonneg.mpr ((sq_le_sq₀ hz.1.le (div_pos hz.1 ht).le).mpr h)
  have hun : 0 ≤ᵐ[volume.restrict (Ico t 1)] (fun z : ℝ => Real.pi * (1 - z ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with z hz
    apply mul_nonneg Real.pi_pos.le
    have hz0 := lt_of_lt_of_le ht hz.1
    nlinarith [hz.2]
  rw [← ofReal_integral_eq_lintegral_ofReal hlint hln,
    ← ofReal_integral_eq_lintegral_ofReal huint hun]
  rw [← ENNReal.ofReal_add (integral_nonneg_of_ae hln) (integral_nonneg_of_ae hun)]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht.le, ← intervalIntegral.integral_of_le ht1]
  simp_rw [div_pow]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      ((intervalIntegral.intervalIntegrable_pow 2).div_const _) (intervalIntegral.intervalIntegrable_pow 2),
    intervalIntegral.integral_div, integral_pow,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      intervalIntegrable_const (intervalIntegral.intervalIntegrable_pow 2),
    intervalIntegral.integral_const, integral_pow]
  simp only [Nat.reduceAdd, Nat.cast_ofNat, zero_pow, sub_zero, one_pow, one_mul]
  field_simp
  <;> ring

lemma sphereArea_projection_eq_coordinate (x : Sphere) (i : Fin 3) :
    Measure.map (fun y : Sphere => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2)
      sphereArea =
    Measure.map (fun y : Sphere => (1 - (y : Ambient) i) / 2) sphereArea := by
  let z : Sphere := ⟨EuclideanSpace.single i (1 : ℝ), by
    simp [mem_sphere_zero_iff_norm, PiLp.norm_single]⟩
  simpa [z, EuclideanSpace.inner_single_left] using sphereArea_projection_independent x z

lemma sphereProjection_raw_north_cap {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (volume : Measure Ambient).toSphere {y : Sphere | t ≤ (y : Ambient) 0} =
      ENNReal.ofReal (2 * Real.pi * (1-t)) := by
  rw [Measure.toSphere_apply' _ (by measurability), sphereProjection_north_cone_volume ht ht1]
  have hd : Module.finrank ℝ Ambient = 3 := by simp [Ambient]
  simp only [hd, Nat.cast_ofNat]
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

lemma sphereProjection_raw_antipodal (t : ℝ) :
    (volume : Measure Ambient).toSphere {y : Sphere | (y : Ambient) 0 ≤ t} =
      (volume : Measure Ambient).toSphere {y : Sphere | -t ≤ (y : Ambient) 0} := by
  let g : Ambient ≃ₗᵢ[ℝ] Ambient := LinearIsometryEquiv.neg ℝ
  have hm : MeasurableSet {y : Sphere | (y : Ambient) 0 ≤ t} := by measurability
  have h := (sphereRotation_preserving g).measure_preimage hm.nullMeasurableSet
  have heq : sphereRotation g ⁻¹' {y : Sphere | (y : Ambient) 0 ≤ t} =
      {y : Sphere | -t ≤ (y : Ambient) 0} := by
    ext y
    simp only [mem_preimage, mem_setOf_eq]
    change -(y : Ambient) 0 ≤ t ↔ -t ≤ (y : Ambient) 0
    constructor <;> intro hy <;> linarith
  rw [heq] at h
  exact h.symm

theorem sphereArea_uniform_projection (x : Sphere) :
    Measure.map (fun y : Sphere => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2)
      sphereArea = (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1) := by
  rw [sphereArea_projection_eq_coordinate x 0]
  apply SphereProjection.projection_of_raw_caps sphereProjection_raw_mass
  exact SphereProjection.raw_lower_caps_of_positive_north
    (volume : Measure Ambient).toSphere sphereProjection_raw_mass
    sphereProjection_raw_antipodal (fun _ ht ht1 => sphereProjection_raw_north_cap ht ht1)

end DedekindZetaZeroFree.ComplexFractionalInverse
