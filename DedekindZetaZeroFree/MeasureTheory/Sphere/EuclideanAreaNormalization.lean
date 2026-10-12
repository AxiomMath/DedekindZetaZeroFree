module
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.RawSphereProjection
open MeasureTheory Set
open scoped Pointwise ENNReal

abbrev rawAmbient := EuclideanSpace ℝ (Fin 3)
abbrev rawSphere := ↥(Metric.sphere (0 : rawAmbient) 1)

noncomputable def rawSphereArea : Measure rawSphere :=
  ((volume : Measure rawAmbient).toSphere Set.univ)⁻¹ •
    (volume : Measure rawAmbient).toSphere

theorem rawSphereArea_isProbabilityMeasure : IsProbabilityMeasure rawSphereArea := by
  constructor
  rw [rawSphereArea, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (Measure.measure_univ_pos.mpr (Measure.toSphere_ne_zero volume)).ne'
    (measure_ne_top _ _)

lemma raw_mass :
    (volume : Measure rawAmbient).toSphere univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [Measure.toSphere_apply_univ, EuclideanSpace.volume_ball_fin_three]
  have hd : Module.finrank ℝ rawAmbient = 3 := by simp [rawAmbient]
  simp only [hd, Nat.cast_ofNat, ENNReal.ofReal_one, one_pow, one_mul]
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring
lemma coordinate_bound (y : rawSphere) (i : Fin 3) :
    -1 ≤ (y : rawAmbient) i ∧ (y : rawAmbient) i ≤ 1 := by
  have h : ‖(y : rawAmbient) i‖ ≤ 1 := by
    calc
      _ ≤ ‖(y : rawAmbient)‖ := PiLp.norm_apply_le _ _
      _ = 1 := mem_sphere_zero_iff_norm.mp y.property
  simpa [Real.norm_eq_abs, abs_le] using h

noncomputable def split : rawAmbient ≃ᵐ ℝ × EuclideanSpace ℝ (Fin 2) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm |>.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))
lemma split_preserving : MeasurePreserving split := by
  exact (PiLp.volume_preserving_ofLp (Fin 3)).trans
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))))
lemma split_symm_apply (z : ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    split.symm (z,w) = WithLp.toLp 2 (Fin.cons z w.ofLp) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [split, MeasurableEquiv.prodCongr] <;> rfl
lemma split_norm_sq (z : ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    ‖split.symm (z,w)‖ ^ 2 = z ^ 2 + ‖w‖ ^ 2 := by
  rw [split_symm_apply]
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]

lemma north_cone (t : ℝ) (i : Fin 3) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' {y : rawSphere | t ≤ (y : rawAmbient) i}) =
      {v : rawAmbient | 0 < ‖v‖ ∧ ‖v‖ < 1 ∧ t * ‖v‖ ≤ v i} := by
  ext v
  constructor
  · rintro ⟨r, hr, _, ⟨y, hy, rfl⟩, rfl⟩
    have hn : ‖r • (y : rawAmbient)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1,
        mem_sphere_zero_iff_norm.mp y.property, mul_one]
    simp only [mem_setOf_eq, hn]
    refine ⟨hr.1, hr.2, ?_⟩
    change t * r ≤ r * (y : rawAmbient) i
    simpa only [mul_comm t r] using mul_le_mul_of_nonneg_left hy hr.1.le
  · rintro ⟨hp, hlt, hi⟩
    let y : rawSphere := ⟨‖v‖⁻¹ • v, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']⟩
    refine ⟨‖v‖, ⟨hp, hlt⟩, y, ⟨y, ?_, rfl⟩, ?_⟩
    · change t ≤ ‖v‖⁻¹ * v i
      exact (le_inv_mul_iff₀ hp).mpr (by simpa only [mul_comm] using hi)
    · simp [y, smul_smul, hp.ne']
lemma north_cone_Fubini (t : ℝ) :
    volume (Ioo (0 : ℝ) 1 • (Subtype.val '' {y : rawSphere | t ≤ (y : rawAmbient) 0})) =
      ∫⁻ z : ℝ, volume {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖split.symm (z,w)‖ ∧
        ‖split.symm (z,w)‖ < 1 ∧
        t * ‖split.symm (z,w)‖ ≤ z} := by
  rw [north_cone]
  have hm : MeasurableSet {v : rawAmbient | 0 < ‖v‖ ∧ ‖v‖ < 1 ∧ t * ‖v‖ ≤ v 0} := by
    measurability
  rw [← split_preserving.symm.measure_preimage hm.nullMeasurableSet]
  rw [Measure.volume_eq_prod, Measure.prod_apply (split.symm.measurable hm)]
  congr 1
lemma north_slice_lower {t z : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hz : 0 < z) (hzt : z < t) :
    {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖split.symm (z,w)‖ ∧
        ‖split.symm (z,w)‖ < 1 ∧
        t * ‖split.symm (z,w)‖ ≤ z} =
      Metric.closedBall 0 (Real.sqrt ((z / t) ^ 2 - z ^ 2)) := by
  have hpos : 0 ≤ (z / t) ^ 2 - z ^ 2 := by
    have h : z ≤ z / t := (le_div_iff₀ ht).mpr (by nlinarith)
    nlinarith [div_pos hz ht]
  ext w
  have hn := split_norm_sq z w
  have hn0 := norm_nonneg (split.symm (z,w))
  have hw0 := norm_nonneg w
  have hs := Real.sq_sqrt hpos
  have hzdiv := div_pos hz ht
  have hdiv : z / t < 1 := (div_lt_one ht).mpr hzt
  rw [Metric.mem_closedBall, dist_zero_right]
  simp only [mem_setOf_eq]
  constructor
  · rintro ⟨_, _, hc⟩
    have hc' : ‖split.symm (z,w)‖ ≤ z / t :=
      (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hc)
    have : ‖w‖ ^ 2 ≤ (Real.sqrt ((z / t) ^ 2 - z ^ 2)) ^ 2 := by
      nlinarith
    exact (sq_le_sq₀ hw0 (Real.sqrt_nonneg _)).mp this
  · intro hw
    have hwsq : ‖w‖ ^ 2 ≤ (Real.sqrt ((z / t) ^ 2 - z ^ 2)) ^ 2 :=
      (sq_le_sq₀ hw0 (Real.sqrt_nonneg _)).mpr hw
    have hnle : ‖split.symm (z,w)‖ ≤ z / t := by
      apply (sq_le_sq₀ hn0 hzdiv.le).mp
      nlinarith
    refine ⟨?_, lt_of_le_of_lt hnle hdiv, ?_⟩
    · nlinarith [sq_pos_of_pos hz]
    · have := (le_div_iff₀ ht).mp hnle
      simpa only [mul_comm] using this
lemma north_slice_upper {t z : ℝ} (ht : 0 < t) (htz : t ≤ z)
    (hz1 : z < 1) :
    {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖split.symm (z,w)‖ ∧
        ‖split.symm (z,w)‖ < 1 ∧
        t * ‖split.symm (z,w)‖ ≤ z} =
      Metric.ball 0 (Real.sqrt (1 - z ^ 2)) := by
  have hz : 0 < z := lt_of_lt_of_le ht htz
  have hpos : 0 < 1 - z ^ 2 := by nlinarith
  ext w
  have hn := split_norm_sq z w
  have hn0 := norm_nonneg (split.symm (z,w))
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
    have hnlt : ‖split.symm (z,w)‖ < 1 := by nlinarith
    refine ⟨?_, hnlt, ?_⟩
    · nlinarith [sq_pos_of_pos hz]
    · calc
        _ ≤ t * 1 := mul_le_mul_of_nonneg_left hnlt.le ht.le
        _ ≤ z := by simpa using htz
lemma north_slice_empty {t z : ℝ} (ht : 0 < t)
    (hz : z ≤ 0 ∨ 1 ≤ z) :
    {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖split.symm (z,w)‖ ∧
        ‖split.symm (z,w)‖ < 1 ∧
        t * ‖split.symm (z,w)‖ ≤ z} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro w
  rintro ⟨hnpos, hnlt, hc⟩
  have hn := split_norm_sq z w
  have hw := sq_nonneg ‖w‖
  have hn0 := norm_nonneg (split.symm (z,w))
  rcases hz with hz | hz
  · nlinarith
  · nlinarith
lemma north_slice_volume_lower {t z : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hz : 0 < z) (hzt : z < t) :
    volume {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖split.symm (z,w)‖ ∧
        ‖split.symm (z,w)‖ < 1 ∧
        t * ‖split.symm (z,w)‖ ≤ z} =
      ENNReal.ofReal (Real.pi * ((z / t) ^ 2 - z ^ 2)) := by
  rw [north_slice_lower ht ht1 hz hzt, EuclideanSpace.volume_closedBall_fin_two]
  have hpos : 0 ≤ (z / t) ^ 2 - z ^ 2 := by
    have h : z ≤ z / t := (le_div_iff₀ ht).mpr (by nlinarith)
    nlinarith [div_pos hz ht]
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hpos,
    ← ENNReal.ofReal_mul hpos, mul_comm]
lemma north_slice_volume_upper {t z : ℝ} (ht : 0 < t) (htz : t ≤ z)
    (hz1 : z < 1) :
    volume {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖split.symm (z,w)‖ ∧
        ‖split.symm (z,w)‖ < 1 ∧
        t * ‖split.symm (z,w)‖ ≤ z} =
      ENNReal.ofReal (Real.pi * (1 - z ^ 2)) := by
  rw [north_slice_upper ht htz hz1, EuclideanSpace.volume_ball_fin_two]
  have hz : 0 < z := lt_of_lt_of_le ht htz
  have hpos : 0 ≤ 1 - z ^ 2 := by nlinarith
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hpos,
    ← ENNReal.ofReal_mul hpos, mul_comm]

lemma north_cone_integrals {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    volume (Ioo (0 : ℝ) 1 • (Subtype.val '' {y : rawSphere | t ≤ (y : rawAmbient) 0})) =
      (∫⁻ z in Ioo 0 t, ENNReal.ofReal (Real.pi * ((z / t) ^ 2 - z ^ 2))) +
      (∫⁻ z in Ico t 1, ENNReal.ofReal (Real.pi * (1 - z ^ 2))) := by
  rw [north_cone_Fubini]
  have heq : (fun z : ℝ => volume {w : EuclideanSpace ℝ (Fin 2) |
        0 < ‖split.symm (z,w)‖ ∧
        ‖split.symm (z,w)‖ < 1 ∧
        t * ‖split.symm (z,w)‖ ≤ z}) =
      (Ioo 0 t).indicator (fun z => ENNReal.ofReal (Real.pi * ((z / t) ^ 2 - z ^ 2))) +
      (Ico t 1).indicator (fun z => ENNReal.ofReal (Real.pi * (1 - z ^ 2))) := by
    ext z
    by_cases hz : 0 < z
    · by_cases hzt : z < t
      · simp only [Pi.add_apply, indicator_of_mem (show z ∈ Ioo 0 t from ⟨hz,hzt⟩)]
        rw [north_slice_volume_lower ht ht1 hz hzt,
          indicator_of_notMem (show z ∉ Ico t 1 from fun h => (not_le.mpr hzt) h.1), add_zero]
      · by_cases hz1 : z < 1
        · rw [north_slice_volume_upper ht (le_of_not_gt hzt) hz1]
          simp [indicator_of_notMem (show z ∉ Ioo 0 t from fun h => hzt h.2),
            indicator_of_mem (show z ∈ Ico t 1 from ⟨le_of_not_gt hzt,hz1⟩)]
        · rw [north_slice_empty ht (Or.inr (le_of_not_gt hz1))]
          simp [indicator_of_notMem (show z ∉ Ioo 0 t from fun h => hzt h.2),
            indicator_of_notMem (show z ∉ Ico t 1 from fun h => hz1 h.2)]
    · rw [north_slice_empty ht (Or.inl (le_of_not_gt hz))]
      simp [indicator_of_notMem (show z ∉ Ioo 0 t from fun h => hz h.1),
        indicator_of_notMem (show z ∉ Ico t 1 from fun h => hz (lt_of_lt_of_le ht h.1))]
  rw [heq]
  change (∫⁻ z, (Ioo 0 t).indicator (fun z => ENNReal.ofReal (Real.pi * ((z / t) ^ 2 - z ^ 2))) z +
    (Ico t 1).indicator (fun z => ENNReal.ofReal (Real.pi * (1 - z ^ 2))) z) = _
  rw [lintegral_add_left
    ((Measurable.ennreal_ofReal (by fun_prop)).indicator measurableSet_Ioo)
    ((Ico t 1).indicator _), lintegral_indicator measurableSet_Ioo,
    lintegral_indicator measurableSet_Ico]
lemma north_cone_volume {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    volume (Ioo (0 : ℝ) 1 • (Subtype.val '' {y : rawSphere | t ≤ (y : rawAmbient) 0})) =
      ENNReal.ofReal (2 * Real.pi / 3 * (1 - t)) := by
  rw [north_cone_integrals ht ht1]
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

noncomputable def rotation (g : rawAmbient ≃ₗᵢ[ℝ] rawAmbient) (x : rawSphere) : rawSphere :=
  ⟨g x, by simpa only [mem_sphere_zero_iff_norm, g.norm_map] using x.property⟩
lemma rotation_continuous (g : rawAmbient ≃ₗᵢ[ℝ] rawAmbient) :
    Continuous (rotation g) := by
  exact (g.continuous.comp continuous_subtype_val).subtype_mk _
lemma rotation_cone_preimage (g : rawAmbient ≃ₗᵢ[ℝ] rawAmbient) (s : Set rawSphere) :
    g ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) =
    Ioo (0 : ℝ) 1 • (Subtype.val '' (rotation g ⁻¹' s)) := by
  ext z
  constructor
  · rintro ⟨r, hr, w, ⟨y, hy, rfl⟩, hz⟩
    refine ⟨r, hr, g.symm y, ⟨rotation g.symm y, ?_, rfl⟩, ?_⟩
    · simpa [rotation] using hy
    · have := congrArg g.symm hz
      simpa using this
  · rintro ⟨r, hr, w, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨r, hr, g y, ⟨rotation g y, hy, rfl⟩, by simp⟩
lemma rotation_preserving (g : rawAmbient ≃ₗᵢ[ℝ] rawAmbient) :
    MeasurePreserving (rotation g) (volume : Measure rawAmbient).toSphere
      (volume : Measure rawAmbient).toSphere := by
  refine ⟨(rotation_continuous g).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (rotation_continuous g).measurable hs,
    Measure.toSphere_apply' _ ((rotation_continuous g).measurable hs),
    Measure.toSphere_apply' _ hs, ← rotation_cone_preimage]
  rw [g.measurePreserving.measure_preimage_emb g.toHomeomorph.measurableEmbedding]

end DedekindZetaZeroFree.ComplexFractionalInverse.RawSphereProjection
