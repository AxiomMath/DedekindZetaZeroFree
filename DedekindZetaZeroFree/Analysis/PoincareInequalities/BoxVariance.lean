module

public import Mathlib

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCubeAverageError

open MeasureTheory

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def box (n : ℕ) (l : Fin n → ℝ) (h : ℝ) : Set (Space n) :=
  {x | ∀ j, l j ≤ x j ∧ x j < l j + h}

noncomputable def axis {n : ℕ} (x : Space n) (j : Fin n) (t : ℝ) : Space n :=
  x + (t - x j) • EuclideanSpace.basisFun (Fin n) ℝ j

noncomputable def mix {n : ℕ} (x y : Space n) (k : ℕ) : Space n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun j => if j.val < k then y j else x j)

variable {I : Type*} [Fintype I] [DecidableEq I]
private theorem hybrid_map (μ : I → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (p : I → Prop) [DecidablePred p] :
    ((Measure.pi μ).prod (Measure.pi μ)).map
      (fun q : (I → ℝ) × (I → ℝ) => fun i => if p i then q.2 i else q.1 i) =
      (Measure.pi μ Set.univ) • Measure.pi μ := by
  let T : ((I → ℝ) × (I → ℝ)) → (I → ℝ) :=
    fun q i => if p i then q.2 i else q.1 i
  have hT : Measurable T := by
    apply measurable_pi_lambda; intro i; dsimp [T]; split_ifs <;> fun_prop
  haveI (i : I) : IsFiniteMeasure ((μ i Set.univ) • μ i) := by
    constructor
    simp only [Measure.smul_apply, smul_eq_mul]
    finiteness
  apply Eq.trans (Measure.pi_eq (μ := fun i => (μ i Set.univ) • μ i) ?_).symm ?_
  · intro s hs
    rw [Measure.map_apply hT (MeasurableSet.univ_pi hs)]
    have he : T ⁻¹' Set.univ.pi s =
        (Set.univ.pi (fun i => if p i then Set.univ else s i)) ×ˢ
        (Set.univ.pi (fun i => if p i then s i else Set.univ)) := by
      ext q; simp [T, Set.mem_pi]; constructor
      · intro H; constructor
        · intro i; by_cases hi : p i
          · simp [hi]
          · simpa [hi] using H i
        · intro i; by_cases hi : p i
          · simpa [hi] using H i
          · simp [hi]
      · rintro ⟨H,K⟩ i; by_cases hi : p i
        · simpa [T, hi] using K i
        · simpa [T, hi] using H i
    rw [he, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro i _
    by_cases hi : p i <;> simp [hi, mul_comm]
  · apply Measure.pi_eq (μ := fun i => (μ i Set.univ) • μ i)
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_univ, Measure.pi_pi,
      Finset.prod_mul_distrib]
private theorem update_map (μ : I → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] (j : I) :
    ((Measure.pi μ).prod (μ j)).map
      (fun q : (I → ℝ) × ℝ => Function.update q.1 j q.2) =
      (μ j Set.univ) • Measure.pi μ := by
  let ν : I → Measure ℝ := fun i => (if i = j then μ j Set.univ else 1) • μ i
  haveI (i : I) : IsFiniteMeasure (ν i) := by
    constructor; simp only [ν, Measure.smul_apply, smul_eq_mul]; split_ifs <;> finiteness
  have hm : Measurable (fun q : (I → ℝ) × ℝ => Function.update q.1 j q.2) := by
    apply measurable_pi_lambda; intro i; by_cases hi : i = j <;> simp [Function.update, hi] <;> fun_prop
  apply Eq.trans (Measure.pi_eq (μ := ν) ?_).symm ?_
  · intro s hs
    rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have he : (fun q : (I → ℝ) × ℝ => Function.update q.1 j q.2) ⁻¹' Set.univ.pi s =
        (Set.univ.pi (Function.update s j Set.univ)) ×ˢ s j := by
      ext q; simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
      constructor
      · intro H; constructor
        · intro i; by_cases hi : i = j
          · simp [hi]
          · simpa [Function.update, hi] using H i
        · simpa using H j
      · rintro ⟨H,K⟩ i; by_cases hi : i = j
        · subst i; simpa using K
        · simpa [Function.update, hi] using H i
    rw [he, Measure.prod_prod, Measure.pi_pi]
    simp only [ν, Measure.smul_apply, smul_eq_mul]
    rw [← Finset.prod_erase_mul _ _ (a := j) (by simp),
      ← Finset.prod_erase_mul Finset.univ (fun i => (if i = j then μ j Set.univ else 1) * μ i (s i))
        (by simp : j ∈ Finset.univ)]
    simp only [Function.update_self, if_pos rfl]
    rw [mul_assoc]
    congr 1
    apply Finset.prod_congr rfl; intro i hi
    simp [Function.update, Finset.ne_of_mem_erase hi]
  · apply Measure.pi_eq (μ := ν)
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, ν, Finset.prod_mul_distrib]
    simp
private theorem hybrid_integral (μ : I → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (p : I → Prop) [DecidablePred p] (j : I) (f : (I → ℝ) → ℝ)
    (hf : StronglyMeasurable f) (hfi : Integrable f (Measure.pi μ)) :
    ∫ x, ∫ y, ∫ t, f (Function.update (fun i => if p i then y i else x i) j t)
      ∂μ j ∂Measure.pi μ ∂Measure.pi μ =
      (Measure.pi μ Set.univ).toReal * (μ j Set.univ).toReal * ∫ z, f z ∂Measure.pi μ := by
  let M := Measure.pi μ
  let U : ((I → ℝ) × ℝ) → (I → ℝ) := fun q => Function.update q.1 j q.2
  have hU : Measurable U := by
    apply measurable_pi_lambda; intro i; dsimp [U]; by_cases hi : i = j <;>
      simp [Function.update, hi] <;> fun_prop
  have hmapU : (M.prod (μ j)).map U = (μ j Set.univ) • M := update_map μ j
  have hfu : Integrable (fun q => f (U q)) (M.prod (μ j)) := by
    apply (integrable_map_measure (hf.aestronglyMeasurable) hU.aemeasurable).mp
    rw [hmapU]; exact hfi.smul_measure (by finiteness)
  let H : (I → ℝ) → ℝ := fun x => ∫ t, f (Function.update x j t) ∂μ j
  have hH : StronglyMeasurable H := (hf.comp_measurable hU).integral_prod_right'
  have hiH : Integrable H M := hfu.integral_prod_left
  let T : ((I → ℝ) × (I → ℝ)) → (I → ℝ) :=
    fun q i => if p i then q.2 i else q.1 i
  have hT : Measurable T := by
    apply measurable_pi_lambda; intro i; dsimp [T]; split_ifs <;> fun_prop
  have hmapT : (M.prod M).map T = (M Set.univ) • M := hybrid_map μ p
  have hHT : Integrable (fun q => H (T q)) (M.prod M) := by
    apply (integrable_map_measure hH.aestronglyMeasurable hT.aemeasurable).mp
    rw [hmapT]; exact hiH.smul_measure (by finiteness)
  change ∫ x, ∫ y, H (T (x,y)) ∂M ∂M = _
  rw [← integral_prod _ hHT, ← integral_map hT.aemeasurable hH.aestronglyMeasurable,
    hmapT, integral_smul_measure]
  change (M Set.univ).toReal * (∫ x, ∫ t, f (U (x,t)) ∂μ j ∂M) = _
  rw [← integral_prod _ hfu, ← integral_map hU.aemeasurable hf.aestronglyMeasurable,
    hmapU, integral_smul_measure]
  simp [M, smul_eq_mul, mul_assoc]

private theorem box_integral_pi (n : ℕ) (l : Fin n → ℝ) (h : ℝ)
    (f : Space n → ℝ) :
    ∫ x in box n l h, f x = ∫ x, f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
      ∂Measure.pi (fun i => volume.restrict (Set.Ico (l i) (l i + h))) := by
  let C := Set.univ.pi (fun i : Fin n => Set.Ico (l i) (l i + h))
  have hp := (PiLp.volume_preserving_ofLp (Fin n)).restrict_preimage
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ico) : MeasurableSet C)
  have hc : (WithLp.ofLp : Space n → Fin n → ℝ) ⁻¹' C = box n l h := by
    ext x; simp [C, box]
  rw [hc] at hp
  have hp' : MeasurePreserving (WithLp.ofLp : Space n → Fin n → ℝ)
      (volume.restrict (box n l h))
      (Measure.pi (fun i => volume.restrict (Set.Ico (l i) (l i + h)))) := by
    convert hp using 1
    exact (Measure.restrict_pi_pi (fun _ : Fin n => (volume : Measure ℝ)) _).symm
  let e := (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
  have ht := hp'.integral_comp e.measurableEmbedding (fun x => f (e.symm x))
  rw [show (fun x : Space n => f (e.symm (WithLp.ofLp x))) = f by
    funext x; exact congrArg f (e.symm_apply_apply x)] at ht
  exact ht

private theorem axis_mix_eq (n : ℕ) (j : Fin n) (x y : Fin n → ℝ) (t : ℝ) :
    axis (mix ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
      ((EuclideanSpace.equiv (Fin n) ℝ).symm y) j.val) j t =
    (EuclideanSpace.equiv (Fin n) ℝ).symm
      (Function.update (fun i => if i.val < j.val then y i else x i) j t) := by
  ext i
  simp [axis, mix, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply,
    Function.update]
  split_ifs <;> simp_all

theorem box_hybrid_line_integral (n : ℕ) (l : Fin n → ℝ) (h : ℝ) (hh : 0 < h)
    (j : Fin n) (g : Space n → ℝ) (hg : Continuous g) :
    ∫ x in box n l h, ∫ y in box n l h,
      ∫ t in Set.Icc (l j) (l j + h), g (axis (mix x y j.val) j t) =
      h * (volume (box n l h)).toReal * ∫ z in box n l h, g z := by
  classical
  let μ : Fin n → Measure ℝ := fun i => volume.restrict (Set.Ico (l i) (l i + h))
  haveI (i : Fin n) : IsFiniteMeasure (μ i) := by
    dsimp [μ]; infer_instance
  let e := (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
  let f : (Fin n → ℝ) → ℝ := fun x => g (e.symm x)
  have hf : Continuous f := hg.comp e.symm.continuous
  have hfi : Integrable f (Measure.pi μ) := by
    rw [← Measure.restrict_pi_pi]
    apply IntegrableOn.mono_set
      (hf.continuousOn.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc)))
    intro x hx i _
    exact ⟨(hx i trivial).1, (hx i trivial).2.le⟩
  have hv : (Measure.pi μ Set.univ).toReal = (volume (box n l h)).toReal := by
    have hp := (PiLp.volume_preserving_ofLp (Fin n)).restrict_preimage
      (MeasurableSet.univ_pi (fun _ => measurableSet_Ico) :
        MeasurableSet (Set.univ.pi (fun i : Fin n => Set.Ico (l i) (l i + h))))
    have hc : (WithLp.ofLp : Space n → Fin n → ℝ) ⁻¹'
        Set.univ.pi (fun i : Fin n => Set.Ico (l i) (l i + h)) = box n l h := by
      ext x; simp [box]
    have ht := hp.measure_preimage (MeasurableSet.univ.nullMeasurableSet)
    simp only [Set.preimage_univ, Measure.restrict_apply_univ] at ht
    rw [hc] at ht
    change (Measure.pi μ Set.univ).toReal = _
    rw [← Measure.restrict_pi_pi, Measure.restrict_apply_univ]
    exact congrArg ENNReal.toReal ht.symm
  have hmj : (μ j Set.univ).toReal = h := by
    simp [μ, Real.volume_Ico, hh.le]
  simp_rw [integral_Icc_eq_integral_Ico]
  rw [box_integral_pi]
  simp_rw [box_integral_pi, axis_mix_eq]
  change (∫ x, ∫ y, ∫ t, f (Function.update
    (fun i => if i.val < j.val then y i else x i) j t) ∂μ j ∂Measure.pi μ ∂Measure.pi μ) = _
  rw [hybrid_integral μ (fun i => i.val < j.val) j f hf.stronglyMeasurable hfi,
    hmj, hv]
  change _ = h * (volume (box n l h)).toReal * ∫ z, f z ∂Measure.pi μ
  ring

end DedekindZetaZeroFree.KPCubeAverageError

end

section
set_option maxHeartbeats 1000000

namespace DedekindZetaZeroFree.KPCubeAverageError

open MeasureTheory

 def closedBox (n : ℕ) (l : Fin n → ℝ) (h : ℝ) : Set (Space n) :=
  {x | ∀ j, l j ≤ x j ∧ x j ≤ l j + h}

private theorem closedBox_compact (n : ℕ) (l : Fin n → ℝ) (h : ℝ) :
    IsCompact (closedBox n l h) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hc : IsCompact {x : Fin n → ℝ | ∀ j, x j ∈ Set.Icc (l j) (l j + h)} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  convert hc.image e.symm.continuous using 1
  ext x
  constructor
  · intro hx
    exact ⟨e x, hx, e.symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

private theorem box_meas (n : ℕ) (l : Fin n → ℝ) (h : ℝ) :
    MeasurableSet (box n l h) := by
  have hc := fun j : Fin n => (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).measurable
  simpa only [box, Set.setOf_forall, Set.setOf_and] using
    MeasurableSet.iInter (fun j =>
      (measurableSet_le measurable_const (hc j)).inter
        (measurableSet_lt (hc j) measurable_const))

private theorem box_subset_closed (n : ℕ) (l : Fin n → ℝ) (h : ℝ) :
    box n l h ⊆ closedBox n l h := fun _ hx j => ⟨(hx j).1, (hx j).2.le⟩

private theorem box_ae_closed (n : ℕ) (l : Fin n → ℝ) (h : ℝ) :
    box n l h =ᵐ[volume] closedBox n l h := by
  have he := (PiLp.volume_preserving_ofLp (Fin n)).quasiMeasurePreserving.ae
    (Measure.univ_pi_Ico_ae_eq_Icc (f := l) (g := fun j => l j + h))
  filter_upwards [he] with x hx
  simpa only [box, closedBox, Set.mem_pi, Set.mem_univ, forall_const,
    Set.mem_Ico, Set.mem_Icc, Pi.le_def, Set.mem_setOf_eq, forall_and] using hx

private theorem box_integrable {n : ℕ} {l : Fin n → ℝ} {h : ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Space n → E} (hg : Continuous g) : IntegrableOn g (box n l h) :=
  (hg.continuousOn.integrableOn_compact (closedBox_compact n l h)).mono_set
    (box_subset_closed n l h)

private theorem box_param_cont {n : ℕ} {l : Fin n → ℝ} {h : ℝ}
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    {g : X → Space n → ℝ} (hg : Continuous (Function.uncurry g)) :
    Continuous (fun x => ∫ y in box n l h, g x y) := by
  have he : (fun x => ∫ y in box n l h, g x y) =
      (fun x => ∫ y in closedBox n l h, g x y) := by
    funext x
    exact setIntegral_congr_set (box_ae_closed n l h)
  rw [he]
  exact continuous_parametric_integral_of_continuous hg (closedBox_compact n l h)

private theorem box_volume (n : ℕ) (l : Fin n → ℝ) (h : ℝ) (hh : 0 < h) :
    volume (box n l h) = ENNReal.ofReal (h ^ n) := by
  have hset : box n l h = WithLp.ofLp ⁻¹'
      (Set.univ.pi (fun j : Fin n => Set.Ico (l j) (l j + h))) := by
    ext x
    simp [box]
  rw [hset, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    ((MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).nullMeasurableSet),
    Real.volume_pi_Ico]
  simp [ENNReal.ofReal_pow hh.le]

private theorem mix_continuous (n k : ℕ) :
    Continuous (fun p : Space n × Space n => mix p.1 p.2 k) := by
  unfold mix
  apply (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp
  apply continuous_pi
  intro j
  split_ifs
  · exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_snd
  · exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_fst

private theorem line_continuous {n : ℕ} (j : Fin n) :
    Continuous (fun p : (Space n × Space n) × ℝ => axis (mix p.1.1 p.1.2 j.val) j p.2) := by
  have hm : Continuous (fun p : (Space n × Space n) × ℝ => mix p.1.1 p.1.2 j.val) :=
    (mix_continuous n j.val).comp continuous_fst
  unfold axis
  exact hm.add ((continuous_snd.sub
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp hm)).smul continuous_const)

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

theorem box_variance_bound_of_pair_bound (n : ℕ) (l : Fin n → ℝ) (h : ℝ)
    (hh : 0 < h) (f : Space n → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hpair : ∀ x ∈ box n l h, ∀ y ∈ box n l h,
      ‖f x - f y‖ ^ 2 ≤ (n : ℝ) * h *
        ∑ j : Fin n, ∫ t in Set.Icc (l j) (l j + h),
          ‖fderiv ℝ f (axis (mix x y j.val) j t)
            (EuclideanSpace.basisFun (Fin n) ℝ j)‖ ^ 2) :
    ∫ x in box n l h,
      ‖f x - ((volume (box n l h)).toReal : ℂ)⁻¹ *
        (∫ y in box n l h, f y)‖ ^ 2 ≤
      (n : ℝ) * h ^ 2 * ∫ x in box n l h,
        ∑ j : Fin n, ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ j)‖ ^ 2 := by
  classical
  let B := box n l h
  let μ := volume.restrict B
  let v := (volume B).toReal
  have hv : 0 < v := by
    dsimp [v, B]
    rw [box_volume n l h hh, ENNReal.toReal_ofReal (by positivity)]
    positivity
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    dsimp [B]
    rw [box_volume n l h hh]
    exact ENNReal.ofReal_ne_top)
  have hμ : (μ Set.univ).toReal = v := by simp [μ, v]
  let c : ℂ := (v : ℂ)⁻¹ * ∫ y, f y ∂μ
  let G : Fin n → Space n → ℝ := fun j x =>
    ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ j)‖ ^ 2
  have hG : ∀ j, Continuous (G j) := fun j =>
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2
  let L : Fin n → Space n × Space n → ℝ := fun j p =>
    ∫ t in Set.Icc (l j) (l j + h), G j (axis (mix p.1 p.2 j.val) j t)
  have hL : ∀ j, Continuous (L j) := by
    intro j
    exact continuous_parametric_integral_of_continuous
      (f := fun (p : Space n × Space n) (t : ℝ) => G j (axis (mix p.1 p.2 j.val) j t))
      ((hG j).comp (line_continuous j)) isCompact_Icc
  have hS : Continuous (fun p : Space n × Space n => ∑ j, L j p) :=
    continuous_finset_sum _ (fun j _ => hL j)
  have hA : Continuous (fun x => ∫ y in B, ∑ j, L j (x, y)) :=
    box_param_cont hS
  have hif : Integrable f μ := box_integrable hf.continuous
  have hdev : Integrable (fun x => ‖f x - c‖ ^ 2) μ :=
    box_integrable ((hf.continuous.sub continuous_const).norm.pow 2)
  have hpoint : ∀ x ∈ B,
      v * ‖f x - c‖ ^ 2 ≤ (n : ℝ) * h * ∫ y, ∑ j, L j (x, y) ∂μ := by
    intro x hx
    have hgc : Continuous (fun y => f x - f y) := continuous_const.sub hf.continuous
    have hg : MemLp (fun y => f x - f y) 2 μ :=
      (memLp_two_iff_integrable_sq_norm hgc.aestronglyMeasurable).2
        (box_integrable (hgc.norm.pow 2))
    have hid : ∫ y, f x - f y ∂μ = v • (f x - c) := by
      rw [integral_sub (integrable_const _) hif, integral_const]
      change (μ Set.univ).toReal • f x - ∫ y, f y ∂μ = v • (f x - c)
      rw [hμ]
      dsimp only [c]
      simp only [Complex.real_smul, smul_eq_mul, mul_sub]
      rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hv.ne'), one_mul]
    have hb := integral_sq_bound hg
    rw [hid, hμ, norm_smul, Real.norm_of_nonneg hv.le, mul_pow] at hb
    have hib : ∫ y, ‖f x - f y‖ ^ 2 ∂μ ≤
        (n : ℝ) * h * ∫ y, ∑ j, L j (x, y) ∂μ := by
      rw [← integral_const_mul]
      apply integral_mono_ae (hg.integrable_norm_pow (by norm_num))
        ((box_integrable (hS.comp (continuous_const.prodMk continuous_id))).const_mul _)
      filter_upwards [ae_restrict_mem (box_meas n l h)] with y hy
      exact hpair x hx y hy
    have hb' := hb.trans (mul_le_mul_of_nonneg_left hib hv.le)
    apply (mul_le_mul_iff_right₀ hv).mp
    convert hb' using 1 <;> ring
  have hbound : v * (∫ x, ‖f x - c‖ ^ 2 ∂μ) ≤
      (n : ℝ) * h * ∫ x, ∫ y, ∑ j, L j (x, y) ∂μ ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_mono_ae (hdev.const_mul _) ((box_integrable hA).const_mul _)
    filter_upwards [ae_restrict_mem (box_meas n l h)] with x hx
    exact hpoint x hx
  have hdouble : (∫ x, ∫ y, ∑ j, L j (x, y) ∂μ ∂μ) =
      h * v * ∫ x, ∑ j, G j x ∂μ := by
    have inner : ∀ x, (∫ y, ∑ j, L j (x, y) ∂μ) =
        ∑ j, ∫ y, L j (x, y) ∂μ := by
      intro x
      exact integral_finset_sum _ (fun j _ =>
        box_integrable ((hL j).comp (continuous_const.prodMk continuous_id)))
    simp_rw [inner]
    rw [integral_finset_sum _ (fun j _ => box_integrable
      (box_param_cont (hL j)))]
    have hj : ∀ j, (∫ x, ∫ y, L j (x, y) ∂μ ∂μ) =
        h * v * ∫ x, G j x ∂μ := by
      intro j
      exact box_hybrid_line_integral n l h hh j (G j) (hG j)
    change (∑ j : Fin n, ∫ x, ∫ y, L j (x, y) ∂μ ∂μ) = _
    simp_rw [hj]
    rw [← Finset.mul_sum, integral_finset_sum _ (fun j _ => box_integrable (hG j))]
  rw [hdouble] at hbound
  change (∫ x, ‖f x - c‖ ^ 2 ∂μ) ≤ (n : ℝ) * h ^ 2 * ∫ x, ∑ j, G j x ∂μ
  apply (mul_le_mul_iff_right₀ hv).mp
  convert hbound using 1 <;> ring

end DedekindZetaZeroFree.KPCubeAverageError

end
