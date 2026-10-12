module

public import DedekindZetaZeroFree.Analysis.PoincareInequalities.BoxVariance
public import DedekindZetaZeroFree.MeasureTheory.Integration.FiniteAlmostEverywherePartitions

@[expose] public section

namespace DedekindZetaZeroFree
namespace KPCubeAverage

open MeasureTheory
open scoped ENNReal

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def cube (n : ℕ) (a : ℝ) : Set (Space n) :=
  {x | ∀ j, -a ≤ x j ∧ x j ≤ a}

noncomputable def cubeMeasure (n : ℕ) (a : ℝ) : Measure (Space n) :=
  volume.restrict (cube n a)

noncomputable abbrev CubeLp (n : ℕ) (a : ℝ) := Lp ℂ 2 (cubeMeasure n a)

abbrev CellIndex (n m : ℕ) := Fin n → Fin m

noncomputable def side (a : ℝ) (m : ℕ) : ℝ := 2 * a / m

noncomputable def cell (n : ℕ) (a : ℝ) (m : ℕ)
    (i : CellIndex n m) : Set (Space n) :=
  {x | ∀ j, -a + (i j : ℝ) * side a m ≤ x j ∧
    x j < -a + ((i j : ℝ) + 1) * side a m}

theorem cube_isCompact (n : ℕ) (a : ℝ) : IsCompact (cube n a) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have h : IsCompact {x : Fin n → ℝ | ∀ j, x j ∈ Set.Icc (-a) a} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  convert h.image e.symm.continuous using 1
  ext x
  constructor
  · intro hx
    exact ⟨e x, hx, e.symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

theorem cell_measurable (n : ℕ) (a : ℝ) (m : ℕ) (i : CellIndex n m) :
    MeasurableSet (cell n a m i) := by
  have h : MeasurableSet (⋂ j : Fin n, {x : Space n |
    -a + (i j : ℝ) * side a m ≤ x j ∧
      x j < -a + ((i j : ℝ) + 1) * side a m}) := MeasurableSet.iInter (fun j : Fin n =>
    (measurableSet_le measurable_const (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).measurable).inter
      (measurableSet_lt (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).measurable measurable_const))
  simpa only [cell, Set.setOf_forall] using h

theorem cell_measure_ne_top (n : ℕ) (a : ℝ) (m : ℕ) (i : CellIndex n m) :
    cubeMeasure n a (cell n a m i) ≠ ⊤ := by
  change (volume.restrict (cube n a)) (cell n a m i) ≠ ⊤
  rw [Measure.restrict_apply (cell_measurable n a m i)]
  exact ne_top_of_le_ne_top ((cube_isCompact n a).measure_ne_top (μ := volume))
    (measure_mono Set.inter_subset_right)

private theorem cell_subset_cube (n : ℕ) (a : ℝ) (ha : 0 < a)
    (m : ℕ) (hm : 1 ≤ m) (i : CellIndex n m) : cell n a m i ⊆ cube n a := by
  intro x hx j
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hs : 0 < side a m := div_pos (by linarith) hmR
  have hmul : (m : ℝ) * side a m = 2 * a := by
    dsimp [side]
    field_simp
  have hi0 : (0 : ℝ) ≤ (i j : ℝ) := by positivity
  have hi1 : (i j : ℝ) + 1 ≤ m := by exact_mod_cast (i j).is_lt
  constructor
  · exact le_trans (by nlinarith) (hx j).1
  · have hh := (hx j).2
    nlinarith [mul_le_mul_of_nonneg_right hi1 (le_of_lt hs)]

private theorem cells_disjoint (n : ℕ) (a : ℝ) (ha : 0 < a) (m : ℕ) (hm : 1 ≤ m) :
    Pairwise (fun i j : CellIndex n m => Disjoint (cell n a m i) (cell n a m j)) := by
  intro i k hik
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hik
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hs : 0 < side a m := div_pos (by linarith) hmR
  apply Set.disjoint_left.mpr
  intro x hxi hxk
  have hi := hxi j
  have hk := hxk j
  rcases lt_or_gt_of_ne hj with h | h
  · have h' : (i j : ℝ) + 1 ≤ (k j : ℝ) := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_right h' hs.le]
  · have h' : (k j : ℝ) + 1 ≤ (i j : ℝ) := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_right h' hs.le]

private theorem interval_cell (a : ℝ) (ha : 0 < a) (m : ℕ) (hm : 1 ≤ m)
    (x : ℝ) (hx : -a ≤ x ∧ x < a) :
    ∃ i : Fin m, -a + (i : ℝ) * side a m ≤ x ∧ x < -a + ((i : ℝ) + 1) * side a m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hs : 0 < side a m := div_pos (by linarith) hmR
  have hmul : (m : ℝ) * side a m = 2 * a := by dsimp [side]; field_simp
  have ht : 0 ≤ (x + a) / side a m := div_nonneg (by linarith [hx.1]) hs.le
  have hlt : (x + a) / side a m < m := (div_lt_iff₀ hs).2 (by linarith [hx.2])
  refine ⟨⟨Nat.floor ((x + a) / side a m), (Nat.floor_lt ht).2 hlt⟩, ?_, ?_⟩
  · have hh := (le_div_iff₀ hs).1 (Nat.floor_le ht)
    dsimp only
    linarith
  · have hh := (div_lt_iff₀ hs).1 (Nat.lt_floor_add_one ((x + a) / side a m))
    dsimp only
    linarith

theorem cell_partition (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 < a)
    (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (CellIndex n m) = m ^ n ∧
    (∀ i, cell n a m i ⊆ cube n a) ∧
    Pairwise (fun i j : CellIndex n m => Disjoint (cell n a m i) (cell n a m j)) ∧
    (∀ᵐ x ∂(volume : Measure (Space n)),
      x ∈ cube n a ↔ x ∈ ⋃ i : CellIndex n m, cell n a m i) ∧
    ∀ i : CellIndex n m,
      volume (cell n a m i) = ENNReal.ofReal (side a m ^ n) ∧
      cubeMeasure n a (cell n a m i) = volume (cell n a m i) := by
  classical
  refine ⟨by simp [CellIndex], cell_subset_cube n a ha m hm,
    cells_disjoint n a ha m hm, ?_, ?_⟩
  · have hpi : (Set.univ.pi (fun _ : Fin n => Set.Ico (-a) a)) =ᵐ[volume]
        Set.Icc (fun _ : Fin n => -a) (fun _ : Fin n => a) :=
      Measure.univ_pi_Ico_ae_eq_Icc
    have he := (PiLp.volume_preserving_ofLp (Fin n)).quasiMeasurePreserving.ae hpi
    filter_upwards [he] with x hx
    have hx' : (∀ j, -a ≤ x j ∧ x j < a) ↔ x ∈ cube n a := by
      simpa only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ico, Set.mem_Icc,
        Pi.le_def, cube, Set.mem_setOf_eq, forall_and] using (iff_of_eq hx)
    constructor
    · intro hxc
      have hc := hx'.2 hxc
      choose i hi using fun j => interval_cell a ha m hm (x j) (hc j)
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    · intro hxc
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hxc
      exact cell_subset_cube n a ha m hm i hi
  · intro i
    refine ⟨?_, ?_⟩
    · have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
      have hs : 0 ≤ side a m := (div_pos (by linarith) hmR).le
      have hset : cell n a m i = WithLp.ofLp ⁻¹' (Set.univ.pi (fun j : Fin n =>
          Set.Ico (-a + (i j : ℝ) * side a m) (-a + ((i j : ℝ) + 1) * side a m))) := by
        ext x
        simp [cell]
      rw [hset, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
        ((MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).nullMeasurableSet),
        Real.volume_pi_Ico]
      have hd : ∀ j : Fin n, (-a + ((i j : ℝ) + 1) * side a m) -
          (-a + (i j : ℝ) * side a m) = side a m := by intro j; ring
      simp_rw [hd]
      simp [ENNReal.ofReal_pow hs]
    · change (volume.restrict (cube n a)) (cell n a m i) = _
      rw [Measure.restrict_apply (cell_measurable n a m i),
        Set.inter_eq_left.mpr (cell_subset_cube n a ha m hm i)]

noncomputable def cellIndicator (n : ℕ) (a : ℝ) (m : ℕ) (i : CellIndex n m) :
    CubeLp n a :=
  indicatorConstLp 2 (cell_measurable n a m i) (cell_measure_ne_top n a m i) (1 : ℂ)

noncomputable def averageOfCells {n : ℕ} {a : ℝ} {I : Type*} [Fintype I]
    (C : I → Set (Space n)) (hC : ∀ i, MeasurableSet (C i))
    (hfin : ∀ i, cubeMeasure n a (C i) ≠ ⊤) : CubeLp n a →L[ℂ] CubeLp n a :=
  ∑ i, let e : CubeLp n a := indicatorConstLp 2 (hC i) (hfin i) (1 : ℂ)
       (((cubeMeasure n a (C i)).toReal : ℂ)⁻¹) • (innerSL ℂ e).smulRight e

noncomputable def average (n : ℕ) (a : ℝ) (m : ℕ) :
    CubeLp n a →L[ℂ] CubeLp n a :=
  averageOfCells (cell n a m) (cell_measurable n a m) (cell_measure_ne_top n a m)

private theorem average_apply (n : ℕ) (a : ℝ) (m : ℕ) (f : CubeLp n a) :
    average n a m f = ∑ i : CellIndex n m,
      (((cubeMeasure n a (cell n a m i)).toReal : ℂ)⁻¹ *
        inner ℂ (cellIndicator n a m i) f) • cellIndicator n a m i := by
  simp [average, averageOfCells, cellIndicator, innerSL_apply_apply, smul_smul]

theorem average_cell_value (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 < a)
    (m : ℕ) (hm : 1 ≤ m) (f : CubeLp n a) (i : CellIndex n m) :
    (∀ᵐ x ∂(volume.restrict (cell n a m i)),
      average n a m f x =
        ((volume (cell n a m i)).toReal : ℂ)⁻¹ *
          ∫ y in cell n a m i, f y ∂volume) := by
  classical
  let c : CellIndex n m → ℂ := fun k =>
    (((cubeMeasure n a (cell n a m k)).toReal : ℂ)⁻¹ *
      inner ℂ (cellIndicator n a m k) f)
  have hle : volume.restrict (cell n a m i) ≤ cubeMeasure n a :=
    Measure.restrict_mono (cell_subset_cube n a ha m hm i) le_rfl
  have hsum := (Lp.coeFn_finsetSum Finset.univ
    (fun k => c k • cellIndicator n a m k)).filter_mono (ae_mono hle)
  have hsmul : ∀ᵐ x ∂(volume.restrict (cell n a m i)), ∀ k : CellIndex n m,
      (c k • cellIndicator n a m k : CubeLp n a) x = c k *
        (cell n a m k).indicator (fun _ => (1 : ℂ)) x := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [(Lp.coeFn_smul (c k) (cellIndicator n a m k)).filter_mono (ae_mono hle),
      (indicatorConstLp_coeFn (p := 2) (hs := cell_measurable n a m k)
        (hμs := cell_measure_ne_top n a m k) (c := (1 : ℂ))).filter_mono (ae_mono hle)] with x hx hy
    rw [hx]
    change c k * (cellIndicator n a m k) x = _
    rw [show (cellIndicator n a m k) x = _ from hy]
  have hci : c i = ((volume (cell n a m i)).toReal : ℂ)⁻¹ *
      ∫ y in cell n a m i, f y ∂volume := by
    dsimp [c]
    rw [cellIndicator, L2.inner_indicatorConstLp_one]
    simp only [cubeMeasure, Measure.restrict_restrict_of_subset (cell_subset_cube n a ha m hm i),
      Measure.restrict_apply (cell_measurable n a m i),
      Set.inter_eq_left.mpr (cell_subset_cube n a ha m hm i)]
  filter_upwards [hsum, hsmul, ae_restrict_mem (cell_measurable n a m i)] with x hx hy hxi
  rw [average_apply]
  change (∑ k, c k • cellIndicator n a m k : CubeLp n a) x = _
  rw [hx]
  simp only [Finset.sum_apply]
  simp_rw [hy]
  rw [Finset.sum_eq_single i]
  · simpa [Set.indicator_of_mem hxi] using hci
  · intro k hk hki
    have hxk : x ∉ cell n a m k := fun hxk =>
      (Set.disjoint_left.mp (cells_disjoint n a ha m hm hki)) hxk hxi
    simp [Set.indicator_of_notMem hxk]
  · simp

theorem average_range (n : ℕ) (a : ℝ) (m : ℕ) :
    LinearMap.range (average n a m).toLinearMap ≤
      Submodule.span ℂ (Set.range (cellIndicator n a m)) := by
  classical
  rintro y ⟨f, rfl⟩
  simp only [average, averageOfCells, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range_self i)

theorem cell_span_finiteDimensional (n : ℕ) (a : ℝ) (m : ℕ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range (cellIndicator n a m))) := by
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

noncomputable def coordinateDerivative (n : ℕ) (f : Space n → ℂ) (j : Fin n) (x : Space n) : ℂ :=
  fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ j)

noncomputable def gradientEnergy (n : ℕ) (f : Space n → ℂ) (x : Space n) : ℝ :=
  ∑ j : Fin n, ‖coordinateDerivative n f j x‖ ^ 2

theorem smooth_memLp (n : ℕ) (a : ℝ) (f : Space n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : MemLp f 2 (cubeMeasure n a) := by
  letI : IsFiniteMeasure (cubeMeasure n a) :=
    isFiniteMeasure_restrict.mpr ((cube_isCompact n a).measure_ne_top (μ := volume))
  obtain ⟨B, hB⟩ := ((cube_isCompact n a).image hf.continuous).isBounded.exists_norm_le
  apply (memLp_top_of_bound hf.continuous.aestronglyMeasurable B ?_).mono_exponent le_top
  filter_upwards [ae_restrict_mem (cube_isCompact n a).measurableSet] with x hx
  exact hB (f x) ⟨x, hx, rfl⟩

theorem smooth_gradient_integrable (n : ℕ) (a : ℝ) (f : Space n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Integrable (gradientEnergy n f) (cubeMeasure n a) := by
  apply ContinuousOn.integrableOn_compact (cube_isCompact n a)
  apply Continuous.continuousOn
  unfold gradientEnergy coordinateDerivative
  apply continuous_finset_sum
  intro j hj
  exact ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2

private theorem norm_toLp_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

private theorem integral_sq_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ (μ Set.univ).toReal * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  let e : Lp ℂ 2 μ := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ _) 1
  have he : ‖e‖ ^ 2 = (μ Set.univ).toReal := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    have hcoe := (indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := measure_ne_top μ _) (c := (1 : ℂ)))
    simp only [Set.indicator_univ, Pi.one_apply] at hcoe
    calc
      (∫ x, inner ℝ (e x) (e x) ∂μ) = ∫ x, (1 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hcoe] with x hx
        change inner ℝ (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ _) (1 : ℂ) x)
          (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ _) (1 : ℂ) x) = 1
        rw [hx]
        norm_num [real_inner_self_eq_norm_sq]
      _ = _ := by simp [Measure.real]
  have hi : inner ℂ e (hf.toLp f) = ∫ x, f x ∂μ := by
    rw [L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top μ _),
      Measure.restrict_univ]
    exact integral_congr_ae hf.coeFn_toLp
  calc
    ‖∫ x, f x ∂μ‖ ^ 2 = ‖inner ℂ e (hf.toLp f)‖ ^ 2 := by rw [hi]
    _ ≤ (‖e‖ * ‖hf.toLp f‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm e _ ) 2
    _ = (μ Set.univ).toReal * ∫ x, ‖f x‖ ^ 2 ∂μ := by
      rw [mul_pow, he, norm_toLp_sq hf]
private theorem interval_pair_bound (l r : ℝ) (hlr : l < r)
    (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x y : ℝ)
    (hx : x ∈ Set.Icc l r) (hy : y ∈ Set.Icc l r) :
    ‖f x - f y‖ ^ 2 ≤ (r - l) * ∫ t in Set.Icc l r, ‖deriv f t‖ ^ 2 := by
  have hd := hf.continuous_deriv (by simp)
  have hi : IntegrableOn (fun t => ‖deriv f t‖ ^ 2) (Set.Icc l r) volume :=
    (hd.norm.pow 2).continuousOn.integrableOn_Icc
  have he : 0 ≤ ∫ t in Set.Icc l r, ‖deriv f t‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  wlog hxy : y ≤ x generalizing x y
  · have h := this y x hy hx (le_of_not_ge hxy)
    simpa only [norm_sub_rev] using h
  have hsub : Set.Ioc y x ⊆ Set.Icc l r := fun t ht => ⟨hy.1.trans ht.1.le, ht.2.trans hx.2⟩
  have hmem : MemLp (deriv f) 2 (volume.restrict (Set.Ioc y x)) := by
    apply (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).2
    exact (show Integrable (fun t => ‖deriv f t‖ ^ 2) (volume.restrict (Set.Icc l r)) from hi).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  have hb := integral_sq_bound hmem
  have hftc : ∫ t in Set.Ioc y x, deriv f t = f x - f y := by
    rw [← intervalIntegral.integral_of_le hxy]
    exact intervalIntegral.integral_deriv_eq_sub
      (fun t ht => (hf.differentiable (by simp)).differentiableAt) (hd.intervalIntegrable _ _)
  rw [hftc, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)] at hb
  have hmon : ∫ t in Set.Ioc y x, ‖deriv f t‖ ^ 2 ≤ ∫ t in Set.Icc l r, ‖deriv f t‖ ^ 2 :=
    integral_mono_measure (Measure.restrict_mono hsub le_rfl)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hi
  calc
    _ ≤ (x - y) * ∫ t in Set.Ioc y x, ‖deriv f t‖ ^ 2 := hb
    _ ≤ (x - y) * ∫ t in Set.Icc l r, ‖deriv f t‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hmon (sub_nonneg.mpr hxy)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [hx.2, hy.1]) he

noncomputable def coordinateLine {n : ℕ} (x : Space n) (j : Fin n) (t : ℝ) : Space n :=
  x + (t - x j) • EuclideanSpace.basisFun (Fin n) ℝ j

theorem coordinateLine_contDiff {n : ℕ} (x : Space n) (j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateLine x j) := by
  unfold coordinateLine
  fun_prop

set_option backward.isDefEq.respectTransparency false in
theorem coordinateLine_hasDerivAt {n : ℕ} (x : Space n) (j : Fin n) (t : ℝ) :
    HasDerivAt (coordinateLine x j) (EuclideanSpace.basisFun (Fin n) ℝ j) t := by
  convert (((((hasDerivAt_id t).sub_const (x j)).smul_const
      (EuclideanSpace.basisFun (Fin n) ℝ j)).const_add x)) using 1
  · funext s; rfl
  · simp only [one_smul]

theorem deriv_coordinateLine {n : ℕ} (f : Space n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Space n) (j : Fin n) (t : ℝ) :
    deriv (f ∘ coordinateLine x j) t = coordinateDerivative n f j (coordinateLine x j t) := by
  exact ((hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
    (coordinateLine_hasDerivAt x j t)).deriv

theorem coordinateLine_apply {n : ℕ} (x : Space n) (j k : Fin n) (t : ℝ) :
    coordinateLine x j t k = if k = j then t else x k := by
  classical
  simp only [coordinateLine, PiLp.add_apply, PiLp.smul_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply, smul_eq_mul]
  split_ifs with h
  · subst k; simp
  · simp [h, Ne.symm h]

noncomputable def coordinateHybrid {n : ℕ} (x y : Space n) (k : ℕ) : Space n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun j => if j.val < k then y j else x j)

theorem coordinateHybrid_apply {n : ℕ} (x y : Space n) (k : ℕ) (j : Fin n) :
    coordinateHybrid x y k j = if j.val < k then y j else x j := rfl

theorem coordinateHybrid_zero {n : ℕ} (x y : Space n) : coordinateHybrid x y 0 = x := by
  ext j
  simp [coordinateHybrid_apply]

theorem coordinateHybrid_last {n : ℕ} (x y : Space n) : coordinateHybrid x y n = y := by
  ext j
  simp [coordinateHybrid_apply, j.is_lt]

theorem coordinateHybrid_step {n : ℕ} (x y : Space n) (j : Fin n) :
    coordinateHybrid x y (j.val + 1) = coordinateLine (coordinateHybrid x y j.val) j (y j) := by
  ext k
  rw [coordinateHybrid_apply, coordinateLine_apply, coordinateHybrid_apply]
  split_ifs <;> simp_all <;> omega

theorem coordinateLine_self {n : ℕ} (x : Space n) (j : Fin n) :
    coordinateLine x j (x j) = x := by
  ext k
  rw [coordinateLine_apply]
  split_ifs with h
  · subst k; rfl
  · rfl

theorem coordinateHybrid_current {n : ℕ} (x y : Space n) (j : Fin n) :
    coordinateHybrid x y j.val j = x j := by
  simp [coordinateHybrid_apply]

theorem telescope_sq_bound {E : Type*} [NormedAddCommGroup E] (n : ℕ) (g : ℕ → E) :
    ‖g 0 - g n‖ ^ 2 ≤ (n : ℝ) * ∑ j ∈ Finset.range n, ‖g j - g (j + 1)‖ ^ 2 := by
  rw [← Finset.sum_range_sub' g n]
  calc
    _ ≤ (∑ j ∈ Finset.range n, ‖g j - g (j + 1)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.range n)
      (f := fun j => ‖g j - g (j + 1)‖))

theorem cell_pair_bound (n : ℕ) (a : ℝ) (ha : 0 < a) (m : ℕ) (hm : 1 ≤ m)
    (i : CellIndex n m) (f : Space n → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x y : Space n) (hx : x ∈ cell n a m i) (hy : y ∈ cell n a m i) :
    ‖f x - f y‖ ^ 2 ≤ (n : ℝ) * side a m *
      ∑ j : Fin n, ∫ t in Set.Icc (-a + (i j : ℝ) * side a m)
        (-a + ((i j : ℝ) + 1) * side a m),
        ‖coordinateDerivative n f j (coordinateLine (coordinateHybrid x y j.val) j t)‖ ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hs : 0 < side a m := div_pos (by linarith) hmR
  have hstep (j : Fin n) :
      ‖f (coordinateHybrid x y j.val) - f (coordinateHybrid x y (j.val + 1))‖ ^ 2 ≤
        side a m * ∫ t in Set.Icc (-a + (i j : ℝ) * side a m)
          (-a + ((i j : ℝ) + 1) * side a m),
          ‖coordinateDerivative n f j (coordinateLine (coordinateHybrid x y j.val) j t)‖ ^ 2 := by
    have h := interval_pair_bound (-a + (i j : ℝ) * side a m)
      (-a + ((i j : ℝ) + 1) * side a m) (by linarith)
      (f ∘ coordinateLine (coordinateHybrid x y j.val) j)
      (hf.comp (coordinateLine_contDiff _ j)) (x j) (y j)
      ⟨(hx j).1, (hx j).2.le⟩ ⟨(hy j).1, (hy j).2.le⟩
    have hlen : -a + ((i j : ℝ) + 1) * side a m -
        (-a + (i j : ℝ) * side a m) = side a m := by ring
    rw [hlen] at h
    simpa only [Function.comp_apply, deriv_coordinateLine f hf,
      ← coordinateHybrid_current x y j, coordinateLine_self, ← coordinateHybrid_step] using h
  have htel := telescope_sq_bound n (fun k => f (coordinateHybrid x y k))
  rw [coordinateHybrid_zero, coordinateHybrid_last] at htel
  calc
    _ ≤ (n : ℝ) * ∑ j : Fin n,
        ‖f (coordinateHybrid x y j.val) - f (coordinateHybrid x y (j.val + 1))‖ ^ 2 := by
      simpa only [← Fin.sum_univ_eq_sum_range] using htel
    _ ≤ (n : ℝ) * ∑ j : Fin n, side a m * ∫ t in Set.Icc
        (-a + (i j : ℝ) * side a m) (-a + ((i j : ℝ) + 1) * side a m),
        ‖coordinateDerivative n f j (coordinateLine (coordinateHybrid x y j.val) j t)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hstep j)) (Nat.cast_nonneg n)
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

theorem average_error_eq_cell_sum (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 < a)
    (m : ℕ) (hm : 1 ≤ m) (f : Space n → ℂ) (hf : MemLp f 2 (cubeMeasure n a)) :
    ‖hf.toLp f - average n a m (hf.toLp f)‖ ^ 2 =
      ∑ i : CellIndex n m, ∫ x in cell n a m i,
        ‖f x - ((volume (cell n a m i)).toReal : ℂ)⁻¹ *
          (∫ y in cell n a m i, f y)‖ ^ 2 := by
  let F := hf.toLp f
  let G := F - average n a m F
  have hi : Integrable (fun x => ‖G x‖ ^ 2) (cubeMeasure n a) :=
    (Lp.memLp G).integrable_norm_pow (by norm_num)
  have hsq : ‖G‖ ^ 2 = ∫ x, ‖G x‖ ^ 2 ∂(cubeMeasure n a) := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun _ => real_inner_self_eq_norm_sq _)
  change ‖G‖ ^ 2 = _
  rw [hsq]
  obtain ⟨_, _, hdisj, hcover, _⟩ := cell_partition n hn a ha m hm
  change ∫ x in cube n a, ‖G x‖ ^ 2 = _
  have hsets : cube n a =ᵐ[volume] ⋃ i, cell n a m i :=
    hcover.mono (fun _ h => propext h)
  rw [Measure.restrict_congr_set hsets]
  rw [integral_iUnion_fintype (fun i => cell_measurable n a m i) hdisj
    (fun i => hi.mono_measure (Measure.restrict_mono (cell_subset_cube n a ha m hm i) le_rfl))]
  apply Finset.sum_congr rfl
  intro i hi'
  have hle : volume.restrict (cell n a m i) ≤ cubeMeasure n a :=
    Measure.restrict_mono (cell_subset_cube n a ha m hm i) le_rfl
  have hcoe := (Lp.coeFn_sub F (average n a m F)).filter_mono (ae_mono hle)
  have hF := hf.coeFn_toLp.filter_mono (ae_mono hle)
  have hav := average_cell_value n hn a ha m hm F i
  have hint : ∫ y in cell n a m i, F y = ∫ y in cell n a m i, f y := integral_congr_ae hF
  apply integral_congr_ae
  filter_upwards [hcoe, hF, hav] with x hx hy hz
  change ‖(F - average n a m F) x‖ ^ 2 = _
  rw [hx, Pi.sub_apply, hz, hint]
  change ‖hf.toLp f x - _‖ ^ 2 = _
  rw [hy]

theorem smooth_error_bound (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 < a)
    (m : ℕ) (hm : 1 ≤ m) (f : Space n → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    let fQ := (smooth_memLp n a f hf).toLp f
    ‖fQ - average n a m fQ‖ ^ 2 ≤
      ((n : ℝ) + 1) ^ 2 * side a m ^ 2 *
        ∫ x, gradientEnergy n f x ∂(cubeMeasure n a) := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hs : 0 < side a m := div_pos (by linarith) hmR
  have hbox (i : CellIndex n m) :
      KPCubeAverageError.box n (fun j => -a + (i j : ℝ) * side a m) (side a m) =
        cell n a m i := by
    have hu (j : Fin n) : -a + (i j : ℝ) * side a m + side a m =
        -a + ((i j : ℝ) + 1) * side a m := by ring
    simp only [KPCubeAverageError.box, cell, hu]
  have hcell (i : CellIndex n m) :
      ∫ x in cell n a m i,
        ‖f x - ((volume (cell n a m i)).toReal : ℂ)⁻¹ *
          (∫ y in cell n a m i, f y)‖ ^ 2 ≤
        (n : ℝ) * side a m ^ 2 * ∫ x in cell n a m i, gradientEnergy n f x := by
    have hu (j : Fin n) : -a + ((i j : ℝ) + 1) * side a m =
        -a + (i j : ℝ) * side a m + side a m := by ring
    have h := KPCubeAverageError.box_variance_bound_of_pair_bound n
      (fun j => -a + (i j : ℝ) * side a m) (side a m) hs f hf (by
        intro x hx y hy
        rw [hbox] at hx hy
        have hp := cell_pair_bound n a ha m hm i f hf x y hx hy
        simp_rw [hu] at hp
        simpa only [KPCubeAverageError.axis, KPCubeAverageError.mix,
          coordinateLine, coordinateHybrid, coordinateDerivative] using hp)
    simpa only [hbox, gradientEnergy, coordinateDerivative] using h
  obtain ⟨_, hsub, hdisj, hcover, _⟩ := cell_partition n hn a ha m hm
  have henergy : ∑ i : CellIndex n m, ∫ x in cell n a m i, gradientEnergy n f x =
      ∫ x, gradientEnergy n f x ∂(cubeMeasure n a) :=
    KPCubeAverageError.integral_finite_ae_partition volume (cube n a) (cell n a m)
      (cell_measurable n a m) hsub hdisj hcover (gradientEnergy n f)
      (smooth_gradient_integrable n a f hf)
  dsimp only
  rw [average_error_eq_cell_sum n hn a ha m hm f (smooth_memLp n a f hf)]
  calc
    _ ≤ ∑ i : CellIndex n m,
        (n : ℝ) * side a m ^ 2 * ∫ x in cell n a m i, gradientEnergy n f x :=
      Finset.sum_le_sum (fun i _ => hcell i)
    _ = (n : ℝ) * side a m ^ 2 *
        ∫ x, gradientEnergy n f x ∂(cubeMeasure n a) := by
      rw [← Finset.mul_sum, henergy]
    _ ≤ _ := by
      have he : 0 ≤ ∫ x, gradientEnergy n f x ∂(cubeMeasure n a) :=
        integral_nonneg (fun x => Finset.sum_nonneg (fun j _ => sq_nonneg _))
      apply mul_le_mul_of_nonneg_right _ he
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith

end KPCubeAverage
end DedekindZetaZeroFree
