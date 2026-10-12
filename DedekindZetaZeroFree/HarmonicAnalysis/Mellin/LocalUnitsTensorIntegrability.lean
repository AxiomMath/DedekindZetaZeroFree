module

public import DedekindZetaZeroFree.Adeles.Archimedean.MixedEmbeddingComparison
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.TraceSchwartzTensors
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.FiniteLocalUnitsIntegrability

@[expose] public section

section

namespace DedekindZetaZeroFree.ProbeSheetGlobalIntegrability
noncomputable section
open MeasureTheory Set

local instance : BorelSpace ℝˣ := ⟨by
  change MeasurableSpace.comap Units.val (borel ℝ) = borel ℝˣ
  rw [Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩

 def shell (a : ℝ) (n : ℕ) : Set ℝˣ :=
  {x | a ^ n ≤ ‖x.val‖ ∧ ‖x.val‖ ≤ 2 * a ^ n}

private lemma compact_shell (a : ℝ) (ha : 0 < a) (n : ℕ) : IsCompact (shell a n) := by
  apply Units.isEmbedding_val₀.isCompact_iff.mpr
  have he : Units.val '' shell a n = {x : ℝ | a ^ n ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * a ^ n} := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx
      have hx0 : x ≠ 0 := by
        intro h; simp [h] at hx
        exact (not_le_of_gt (pow_pos ha n)) hx.1
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [he]
  have h := (isCompact_closedBall (0 : ℝ) (2 * a ^ n)).inter_left
    (isClosed_le continuous_const continuous_norm : IsClosed {x : ℝ | a ^ n ≤ ‖x‖})
  simpa only [Metric.closedBall, dist_zero_right, setOf_and] using h

private lemma measure_shell (ν : Measure ℝˣ) [ν.IsHaarMeasure]
    (a : ℝ) (ha : 0 < a) (n : ℕ) : ν (shell a n) = ν (shell a 0) := by
  let u : ℝˣ := Units.mk0 (a ^ n) (ne_of_gt (pow_pos ha n))
  have he : (fun x : ℝˣ => u * x) ⁻¹' shell a n = shell a 0 := by
    ext x
    simp only [shell, mem_preimage, mem_setOf_eq, Units.val_mul, u, Units.val_mk0,
      norm_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos ha n), pow_zero, mul_one]
    constructor
    · intro h
      exact ⟨(le_mul_iff_one_le_right (pow_pos ha n)).mp h.1,
        (mul_le_mul_iff_right₀ (pow_pos ha n)).mp (by simpa [mul_comm] using h.2)⟩
    · intro h
      constructor
      · exact (le_mul_iff_one_le_right (pow_pos ha n)).mpr h.1
      · simpa [mul_comm] using (mul_le_mul_of_nonneg_right h.2 (pow_pos ha n).le)
  rw [← he, measure_preimage_mul]

private lemma shell_integrable (ν : Measure ℝˣ) [ν.IsHaarMeasure]
    (f : ℝˣ → ℂ) (hf : Continuous f)
    (a : ℝ) (ha : 0 < a) (B r : ℝ) (hB : 0 ≤ B) (hr0 : 0 ≤ r) (hr : r < 1)
    (hb : ∀ n, ∀ x ∈ shell a n, ‖f x‖ ≤ B * r ^ n) :
    IntegrableOn f (⋃ n, shell a n) ν := by
  have hc := compact_shell a ha
  have hi : ∀ n, IntegrableOn f (shell a n) ν :=
    fun n => hf.continuousOn.integrableOn_compact (hc n)
  apply integrableOn_iUnion_of_summable_integral_norm hi
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _))
    (fun n => ?_) ((summable_geometric_of_lt_one hr0 hr).mul_left (ν.real (shell a 0) * B))
  calc
    (∫ x in shell a n, ‖f x‖ ∂ν) ≤ ∫ _ in shell a n, B * r ^ n ∂ν :=
      integral_mono_ae (hi n).norm (integrableOn_const (hc n).measure_lt_top.ne)
        ((ae_restrict_mem (hc n).measurableSet).mono (fun x hx => hb n x hx))
    _ = (ν.real (shell a 0) * B) * r ^ n := by
      simp [measureReal_def, measure_shell ν a ha n, mul_assoc]

private lemma weight_norm (g : SchwartzMap ℝ ℂ) (z : ℂ) (x : ℝˣ) :
    ‖g x.val * ((‖x.val‖ ^ 2 : ℝ) : ℂ) ^ z‖ = ‖g x.val‖ * ‖x.val‖ ^ (2 * z.re) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (pow_pos (norm_pos_iff.mpr x.ne_zero) 2)]
  congr 1
  exact (Real.rpow_natCast_mul (norm_nonneg _) 2 z.re).symm

private lemma weighted_bound (g : SchwartzMap ℝ ℂ) (z : ℂ) (x : ℝˣ) (k : ℕ) :
    ‖g x.val * ((‖x.val‖ ^ 2 : ℝ) : ℂ) ^ z‖ ≤
      SchwartzMap.seminorm ℝ k 0 g * ‖x.val‖ ^ (2 * z.re - k) := by
  rw [weight_norm]
  have hx : 0 < ‖x.val‖ := norm_pos_iff.mpr x.ne_zero
  have h := mul_le_mul_of_nonneg_right (g.norm_pow_mul_le_seminorm ℝ k x.val)
    (Real.rpow_nonneg hx.le (2 * z.re - k))
  calc
    ‖g x.val‖ * ‖x.val‖ ^ (2 * z.re) =
        (‖x.val‖ ^ k * ‖g x.val‖) * ‖x.val‖ ^ (2 * z.re - k) := by
      rw [← Real.rpow_natCast, mul_right_comm, ← Real.rpow_add hx,
        show (k : ℝ) + (2 * z.re - k) = 2 * z.re by ring]
      exact mul_comm _ _
    _ ≤ _ := h

private lemma cover : (⋃ n, shell (1/2) n) ∪ (⋃ n, shell 2 n) = (univ : Set ℝˣ) := by
  apply eq_univ_of_forall
  intro x
  have hx : 0 < ‖x.val‖ := norm_pos_iff.mpr x.ne_zero
  by_cases hx1 : 1 ≤ ‖x.val‖
  · obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hx1 (by norm_num : (1 : ℝ) < 2)
    exact Or.inr (mem_iUnion.mpr ⟨n, hn, by simpa [pow_succ, mul_comm] using hn'.le⟩)
  · obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one hx (le_of_not_ge hx1)
      (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
    exact Or.inl (mem_iUnion.mpr ⟨n+1, hn.le, by
      have he : (2 : ℝ) * (1/2) ^ (n+1) = (1/2) ^ n := by rw [pow_succ]; ring
      rwa [he]⟩)

theorem schwartz_realUnitsMellin_integrable
    (g : SchwartzMap ℝ ℂ) (ν : Measure ℝˣ) [ν.IsHaarMeasure]
    (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : ℝˣ => g x.val * ((‖x.val‖ ^ 2 : ℝ) : ℂ) ^ z) ν := by
  let f : ℝˣ → ℂ := fun x => g x.val * ((‖x.val‖ ^ 2 : ℝ) : ℂ) ^ z
  have hf : Continuous f := g.continuous.comp Units.continuous_val |>.mul
    ((Complex.continuous_ofReal_cpow_const hz).comp (Units.continuous_val.norm.pow 2))
  have hs : 0 < 2 * z.re := by positivity
  have hsmall : IntegrableOn f (⋃ n, shell (1/2) n) ν := by
    apply shell_integrable ν f hf (1/2) (by norm_num)
      (SchwartzMap.seminorm ℝ 0 0 g * 2 ^ (2 * z.re)) ((1/2) ^ (2 * z.re))
      (by positivity) (by positivity) (Real.rpow_lt_one (by norm_num) (by norm_num) hs)
    intro n x hx
    change (1/2 : ℝ) ^ n ≤ ‖x.val‖ ∧ ‖x.val‖ ≤ 2 * (1/2) ^ n at hx
    change ‖g x.val * ((‖x.val‖ ^ 2 : ℝ) : ℂ) ^ z‖ ≤ _
    rw [weight_norm]
    calc
      ‖g x.val‖ * ‖x.val‖ ^ (2 * z.re) ≤
          SchwartzMap.seminorm ℝ 0 0 g * (2 * (1/2 : ℝ) ^ n) ^ (2 * z.re) :=
        mul_le_mul (g.norm_le_seminorm ℝ x.val)
          (Real.rpow_le_rpow (norm_nonneg _) hx.2 hs.le) (by positivity) (by positivity)
      _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity),
        ← Real.rpow_pow_comm (by norm_num)]; ring
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * z.re)
  have hlarge : IntegrableOn f (⋃ n, shell 2 n) ν := by
    apply shell_integrable ν f hf 2 (by norm_num)
      (SchwartzMap.seminorm ℝ k 0 g) (2 ^ (2 * z.re - k))
      (by positivity) (by positivity)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hk))
    intro n x hx
    change (2 : ℝ) ^ n ≤ ‖x.val‖ ∧ ‖x.val‖ ≤ 2 * 2 ^ n at hx
    apply (weighted_bound g z x k).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.rpow_pow_comm (by norm_num)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hx.1 (sub_nonpos.mpr hk.le)
  have hi := hsmall.union hlarge
  rwa [cover, integrableOn_univ] at hi

end
end DedekindZetaZeroFree.ProbeSheetGlobalIntegrability

end

section

namespace DedekindZetaZeroFree.ProbeSheetGlobalIntegrability
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

variable (F : Type) [Field F] [NumberField F]
 local instance adicCompletionMeasurableSpaceLocalUnitsTensorIntegrability (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
 local instance adicCompletionBorelSpaceLocalUnitsTensorIntegrability (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

 def prodUnitsC (M N : Type*) [Monoid M] [Monoid N]
    [TopologicalSpace M] [TopologicalSpace N] : (M × N)ˣ ≃ₜ* Mˣ × Nˣ where
  __ := MulEquiv.prodUnits
  continuous_toFun := Homeomorph.prodUnits.continuous
  continuous_invFun := Homeomorph.prodUnits.symm.continuous

 def prodCongrC {M N P Q : Type*} [Monoid M] [Monoid N] [Monoid P] [Monoid Q]
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P] [TopologicalSpace Q]
    (e : M ≃ₜ* N) (f : P ≃ₜ* Q) : M × P ≃ₜ* N × Q where
  __ := e.toMulEquiv.prodCongr f.toMulEquiv
  continuous_toFun := e.continuous.prodMap f.continuous
  continuous_invFun := e.symm.continuous.prodMap f.symm.continuous

 def archC : InfiniteAdeleRing F ≃ₜ* mixedEmbedding.mixedSpace F where
  __ := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toMulEquiv
  continuous_toFun := (sArchModel_comparison F).1
  continuous_invFun := (sArchModel_comparison F).2.1

 def coordinates (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (SLocalProduct F S)ˣ ≃ₜ*
      ((({v : InfinitePlace F // v.IsReal} → ℝˣ) ×
        ({v : InfinitePlace F // v.IsComplex} → ℂˣ)) ×
        ((v : S) → (v.val.adicCompletion F)ˣ)) :=
  (prodUnitsC _ _).trans (prodCongrC
    ((Units.mapContinuousMulEquiv (archC F)).trans
      ((prodUnitsC _ _).trans
        (prodCongrC ContinuousMulEquiv.piUnits ContinuousMulEquiv.piUnits)))
    ContinuousMulEquiv.piUnits)

 lemma unitsBorel {K : Type*} [Monoid K] [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K]
    (he : Topology.IsEmbedding (Units.val : Kˣ → K)) : BorelSpace Kˣ := ⟨by
  change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
  rw [BorelSpace.measurable_eq (α := K), he.isInducing.eq_induced, borel_comap]⟩

 local instance fieldUnitsBorel {K : Type*} [Field K] [TopologicalSpace K]
    [ContinuousInv₀ K] [MeasurableSpace K] [BorelSpace K] : BorelSpace Kˣ :=
  unitsBorel Units.isEmbedding_val₀

private lemma cpow_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (z : ℂ) :
    ((∏ i ∈ s, a i : ℝ) : ℂ) ^ z = ∏ i ∈ s, (a i : ℂ) ^ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (ha i (by simp))
      (Finset.prod_nonneg (s := s) (fun j hj => ha j (by simp [hj]))),
      ih (fun j hj => ha j (by simp [hj])), Finset.prod_insert hi]

private lemma archNormProd (a : InfiniteAdeleRing F) :
    (∏ v : InfinitePlace F, ‖a v‖ ^ 2) =
      (∏ v : {v : InfinitePlace F // v.IsReal},
        ‖((InfiniteAdeleRing.ringEquiv_mixedSpace F a).1 v)‖ ^ 2) *
      (∏ v : {v : InfinitePlace F // v.IsComplex},
        ‖((InfiniteAdeleRing.ringEquiv_mixedSpace F a).2 v)‖ ^ 2) := by
  classical
  have hr (v : {v : InfinitePlace F // v.IsReal}) :
      ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F a).1 v‖ = ‖a v‖ :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.prop).norm_map_of_map_zero
      (map_zero _) _
  have hc (v : {v : InfinitePlace F // v.IsComplex}) :
      ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F a).2 v‖ = ‖a v‖ :=
    (InfinitePlace.Completion.isometry_extensionEmbedding v.val).norm_map_of_map_zero
      (map_zero _) _
  simp_rw [hr, hc]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : InfinitePlace F => v.IsReal)]
  congr 1
  exact Fintype.prod_equiv (Equiv.subtypeEquivRight (fun v : InfinitePlace F =>
    v.not_isReal_iff_isComplex)) _ _ (fun _ => rfl)

theorem tensor_units_mellin_integrable
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : SLocalProduct F S → ℂ) (c : ℂ)
    (gReal : (v : {v : InfinitePlace F // v.IsReal}) → ℝ → ℂ)
    (gComplex : (v : {v : InfinitePlace F // v.IsComplex}) → ℂ → ℂ)
    (gFinite : (v : ↥S) → v.val.adicCompletion F → ℂ)
    (htensor : ∀ x, h x = c *
      ((∏ v, gReal v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 v)) *
       (∏ v, gComplex v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v)) *
       ∏ v : ↥S, gFinite v (x.2 v)))
    (z : ℂ)
    (hReal : ∀ v (ν : Measure ℝˣ), ν.IsHaarMeasure →
      Integrable (fun x : ℝˣ => gReal v x.val * ((‖x.val‖ ^ 2 : ℝ) : ℂ) ^ z) ν)
    (hComplex : ∀ v (ν : Measure ℂˣ), ν.IsHaarMeasure →
      Integrable (fun x : ℂˣ => gComplex v x.val * ((‖x.val‖ ^ 2 : ℝ) : ℂ) ^ z) ν)
    (hFinite : ∀ v (ν : Measure (v.val.adicCompletion F)ˣ), ν.IsHaarMeasure →
      Integrable (fun x : (v.val.adicCompletion F)ˣ =>
        gFinite v x.val * (‖x.val‖ : ℂ) ^ z) ν)
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (hν : @Measure.IsHaarMeasure (SLocalProduct F S)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)) ν) :
    Integrable (fun y : (SLocalProduct F S)ˣ =>
      h y.val * (ProbeWeight.modulus F S y : ℂ) ^ z) ν := by
  classical
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : ∀ v : S, TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    fun v => TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI : ∀ v : S, SecondCountableTopology (v.val.adicCompletion F) := fun _ => inferInstance
  letI : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  letI : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  letI : ∀ v : S, SecondCountableTopology (v.val.adicCompletion F)ˣ := fun _ =>
    Units.isEmbedding_val₀.secondCountableTopology
  let e := coordinates F S
  letI : SecondCountableTopology (SLocalProduct F S)ˣ :=
    e.toHomeomorph.secondCountableTopology
  letI : MeasurableSpace (SLocalProduct F S) := borel _
  letI : BorelSpace (SLocalProduct F S) := ⟨rfl⟩
  have hb : BorelSpace (SLocalProduct F S)ˣ := by
    apply unitsBorel
    let e0 := (prodUnitsC (InfiniteAdeleRing F) ((v : S) → v.val.adicCompletion F)).trans
      (prodCongrC ContinuousMulEquiv.piUnits ContinuousMulEquiv.piUnits)
    have hi := ((Topology.IsEmbedding.piMap (fun v : InfinitePlace F =>
      (Units.isEmbedding_val₀ (G₀ := v.Completion)))).prodMap
      (Topology.IsEmbedding.piMap (fun v : S =>
        (Units.isEmbedding_val₀ (G₀ := v.val.adicCompletion F)))))
    exact hi.comp e0.toHomeomorph.isEmbedding
  letI := hb
  letI := hν
  let μR : Measure ℝˣ := Measure.haar
  let μC : Measure ℂˣ := Measure.haar
  let μF : (v : S) → Measure (v.val.adicCompletion F)ˣ := fun _ => Measure.haar
  let μ := ((Measure.pi (fun _ : {v : InfinitePlace F // v.IsReal} => μR)).prod
    (Measure.pi (fun _ : {v : InfinitePlace F // v.IsComplex} => μC))).prod
      (Measure.pi μF)
  let kR := fun (v : {v : InfinitePlace F // v.IsReal}) (x : ℝˣ) =>
    gReal v x.val * ((‖x.val‖ ^ 2 : ℝ) : ℂ) ^ z
  let kC := fun (v : {v : InfinitePlace F // v.IsComplex}) (x : ℂˣ) =>
    gComplex v x.val * ((‖x.val‖ ^ 2 : ℝ) : ℂ) ^ z
  let kF := fun (v : S) (x : (v.val.adicCompletion F)ˣ) =>
    gFinite v x.val * (‖x.val‖ : ℂ) ^ z
  let k := fun p : (({v : InfinitePlace F // v.IsReal} → ℝˣ) ×
    ({v : InfinitePlace F // v.IsComplex} → ℂˣ)) ×
      ((v : S) → (v.val.adicCompletion F)ˣ) => c * (((∏ v, kR v (p.1.1 v)) * (∏ v, kC v (p.1.2 v))) *
    ∏ v : S, kF v (p.2 v))
  have hk : Integrable k μ := by
    exact (((Integrable.fintype_prod (fun v => hReal v μR inferInstance)).mul_prod
      (Integrable.fintype_prod (fun v => hComplex v μC inferInstance))).mul_prod
        (Integrable.fintype_prod_dep (fun v => hFinite v (μF v) inferInstance))).const_mul c
  have hμR : μR.IsHaarMeasure := by dsimp [μR]; infer_instance
  have hμC : μC.IsHaarMeasure := by dsimp [μC]; infer_instance
  have hμF : ∀ v, (μF v).IsHaarMeasure := by intro v; dsimp [μF]; infer_instance
  letI := hμR
  letI := hμC
  letI := hμF
  have hmulR : MeasurableMul ℝˣ := inferInstance
  have hmulC : MeasurableMul ℂˣ := inferInstance
  have hmulF : ∀ v : S, MeasurableMul (v.val.adicCompletion F)ˣ := fun _ => inferInstance
  have hμ : μ.IsHaarMeasure := by
    dsimp only [μ]
    exact Measure.prod.instIsHaarMeasure _ _
  letI := hμ
  let ν' := Measure.map e ν
  have hν' : ν'.IsHaarMeasure := e.isHaarMeasure_map ν
  letI := hν'
  have hk' : Integrable k ν' := by
    rw [Measure.isMulLeftInvariant_eq_smul ν' μ]
    exact hk.smul_measure_nnreal
  have hcomp := e.toHomeomorph.measurableEmbedding.integrable_map_iff.mp hk'
  apply hcomp.congr
  filter_upwards [] with y
  dsimp [Function.comp_def, k, kR, kC, kF]
  change c * (((∏ v, gReal v ((InfiniteAdeleRing.ringEquiv_mixedSpace F y.val.1).1 v) *
    ((‖(InfiniteAdeleRing.ringEquiv_mixedSpace F y.val.1).1 v‖ ^ 2 : ℝ) : ℂ) ^ z) *
    (∏ v, gComplex v ((InfiniteAdeleRing.ringEquiv_mixedSpace F y.val.1).2 v) *
    ((‖(InfiniteAdeleRing.ringEquiv_mixedSpace F y.val.1).2 v‖ ^ 2 : ℝ) : ℂ) ^ z)) *
    ∏ v : S, gFinite v (y.val.2 v) * (‖y.val.2 v‖ : ℂ) ^ z) = _
  rw [htensor]
  simp only [Finset.prod_mul_distrib]
  rw [ProbeWeight.modulus, archNormProd F]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
    (mul_nonneg (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
      (Finset.prod_nonneg (fun _ _ => sq_nonneg _)))
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
    (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
    (Finset.prod_nonneg (fun _ _ => sq_nonneg _))]
  rw [cpow_prod _ _ (fun _ _ => sq_nonneg _) z,
    cpow_prod _ _ (fun _ _ => sq_nonneg _) z,
    cpow_prod _ _ (fun _ _ => norm_nonneg _) z]
  ring

end
end DedekindZetaZeroFree.ProbeSheetGlobalIntegrability

end

section
namespace DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory
variable {F : Type} [Field F] [NumberField F]

theorem schwartz_complexNormMellin_integrable
    (g : SchwartzMap ℂ ℂ) (μ : Measure ℂ) [μ.IsAddHaarMeasure]
    (s : ℝ) (hs : 0 < s) :
    Integrable (complexNormMellinIntegrand g s) μ := by
  have hmeas : AEStronglyMeasurable (complexNormMellinIntegrand g s) μ := by
    apply Measurable.aestronglyMeasurable
    exact Measurable.ite (measurableSet_singleton 0) measurable_const
      (g.continuous.measurable.mul (Complex.measurable_ofReal.comp
        ((measurable_norm.pow_const 2).pow_const _)))
  have hnorm (x : ℂ) (hx : x ≠ 0) :
      ‖complexNormMellinIntegrand g s x‖ = ‖g x‖ * ‖x‖ ^ (2 * (s - 1)) := by
    simp only [complexNormMellinIntegrand, if_neg hx, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (sq_nonneg _) _)]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (norm_nonneg x)]
    norm_num
  have hnear : IntegrableOn (complexNormMellinIntegrand g s)
      (Metric.ball 0 1) μ := by
    apply integrableOn_ball_of_norm_le_rpow (by simp)
      (C := SchwartzMap.seminorm ℂ 0 0 g) (α := 2 * (1 - s))
      (by simp; linarith) _ hmeas
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x = 0
    · simp only [hx, complexNormMellinIntegrand, ↓reduceIte, norm_zero]
      exact mul_nonneg (apply_nonneg _ _) (Real.rpow_nonneg (by norm_num) _)
    · rw [hnorm x hx]
      rw [show -(2 * (1 - s)) = 2 * (s - 1) by ring]
      exact mul_le_mul_of_nonneg_right (g.norm_le_seminorm ℂ x)
        (Real.rpow_nonneg (norm_nonneg x) _)
  obtain ⟨k, hk⟩ := exists_nat_ge (2 * (s - 1))
  have hfar : IntegrableOn (complexNormMellinIntegrand g s)
      (Metric.ball 0 1)ᶜ μ := by
    apply (g.integrable_pow_mul μ k).restrict.mono' hmeas.restrict
    filter_upwards [self_mem_ae_restrict (measurableSet_ball.compl)] with x hx
    have hnx : 1 ≤ ‖x‖ := by simpa using hx
    have hx0 : x ≠ 0 := by intro h; norm_num [h] at hnx
    rw [hnorm x hx0, mul_comm (‖x‖ ^ k)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg (g x))
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hnx hk
  simpa using hnear.union hfar

theorem schwartz_complexMellin_withDensity_integrable
    (g : SchwartzMap ℂ ℂ) (μ : Measure ℂ) [μ.IsAddHaarMeasure]
    (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : ℂ => g x * ((‖x‖ ^ 2 : ℝ) : ℂ) ^ z)
      ((μ : Measure ℂ).withDensity
        (fun x => ENNReal.ofReal ((Real.pi * ‖x‖ ^ 2)⁻¹))) := by
  have hd : Measurable (fun x : ℂ => ENNReal.ofReal ((Real.pi * ‖x‖ ^ 2)⁻¹)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [integrable_withDensity_iff_integrable_smul₀' hd.aemeasurable
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  have hm : AEStronglyMeasurable (fun x : ℂ =>
      (Real.pi * ‖x‖ ^ 2)⁻¹ • (g x * ((‖x‖ ^ 2 : ℝ) : ℂ) ^ z)) μ := by
    apply Measurable.aestronglyMeasurable
    exact (by fun_prop : Measurable (fun x : ℂ => (Real.pi * ‖x‖ ^ 2)⁻¹)).smul
      (g.continuous.mul ((Complex.continuous_ofReal_cpow_const hz).comp
        (continuous_norm.pow 2))).measurable
  have hbound := (schwartz_complexNormMellin_integrable g μ z.re hz).norm.const_mul Real.pi⁻¹
  apply hbound.mono' ?_ ?_
  · convert hm using 1
    funext x
    rw [ENNReal.toReal_ofReal (by positivity)]
  · apply Filter.Eventually.of_forall
    intro x
    rw [ENNReal.toReal_ofReal (by positivity)]
    by_cases hx : x = 0
    · subst x
      simp [complexNormMellinIntegrand]
    · have hn : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
      simp only [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (Real.pi * ‖x‖ ^ 2)⁻¹), norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hn, complexNormMellinIntegrand,
        if_neg hx, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hn.le _)]
      rw [mul_inv_rev, Real.rpow_sub hn, Real.rpow_one]
      exact le_of_eq (by ring)

theorem schwartz_complexUnitsMellin_integrable
    (g : SchwartzMap ℂ ℂ) (μ : Measure ℂ) [μ.IsAddHaarMeasure]
    (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : ℂˣ => g x.val * ((‖x.val‖ ^ 2 : ℝ) : ℂ) ^ z)
      (Measure.comap Units.val
        (μ.withDensity (fun x => ENNReal.ofReal ((Real.pi * ‖x‖ ^ 2)⁻¹)))) := by
  letI : BorelSpace ℂˣ := ⟨by
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace ℂ) = borel ℂˣ
    rw [(Units.isEmbedding_val₀ (G₀ := ℂ)).eq_induced, borel_comap]
    rfl⟩
  have he : MeasurableEmbedding (Units.val : ℂˣ → ℂ) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.measurableEmbedding
  exact he.integrableOn_range_iff_comap.mp
    (schwartz_complexMellin_withDensity_integrable g μ z hz).integrableOn

theorem integrable_of_isHaarMeasure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    {f : G → ℂ} (hf : Integrable f μ) : Integrable f ν := by
  rw [Measure.isMulLeftInvariant_eq_smul ν μ]
  exact hf.smul_measure ENNReal.coe_ne_top

private theorem complex_addHaar_map_mul (μ : Measure ℂ) [μ.IsAddHaarMeasure] (c : ℂ) (hc : c ≠ 0) :
    μ.map (fun x => c*x) = (ENNReal.ofReal (‖c‖ ^ 2))⁻¹ • μ := by
  let L : ℂ →ₗ[ℝ] ℂ := Algebra.lmul ℝ ℂ c
  have hdet : L.det = ‖c‖ ^ 2 := by
    rw [← LinearMap.det_toMatrix Complex.basisOneI]
    have hmat : LinearMap.toMatrix Complex.basisOneI Complex.basisOneI L =
        !![c.re, -c.im; c.im, c.re] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [LinearMap.toMatrix_apply, L, Complex.basisOneI]
    rw [hmat, Matrix.det_fin_two, Complex.sq_norm]
    simp [Complex.normSq_apply]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar μ
    (f := L) (by rw [hdet]; positivity)
  convert hmap using 1
  · rfl
  · rw [hdet, abs_of_nonneg (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]

private theorem complexUnits_density_left (μ : Measure ℂ) [μ.IsAddHaarMeasure] :
    (Measure.comap Units.val
      (μ.withDensity (fun x : ℂ => ENNReal.ofReal ((Real.pi * ‖x‖ ^ 2)⁻¹)))).IsMulLeftInvariant := by
  letI : BorelSpace ℂˣ := ⟨by
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace ℂ) = borel ℂˣ
    rw [(Units.isEmbedding_val₀ (G₀ := ℂ)).eq_induced, borel_comap]
    rfl⟩
  let ev := (IsOpenUnits.isOpenEmbedding_unitsVal (M := ℂ)).measurableEmbedding
  let D := fun x : ℂ => ENNReal.ofReal ((Real.pi * ‖x‖ ^ 2)⁻¹)
  have hD : Measurable D := by dsimp [D]; fun_prop
  constructor
  intro g
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs]
  change (μ.withDensity D).comap Units.val ((fun x => g * x) ⁻¹' s) =
    (μ.withDensity D).comap Units.val s
  rw [ev.comap_apply, ev.comap_apply]
  have hpre : Units.val '' ((fun x => g * x) ⁻¹' s) =
      (fun x : ℂ => (g : ℂ) * x) ⁻¹' (Units.val '' s) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨g * u, hu, by simp⟩
    · rintro ⟨u, hu, he⟩
      refine ⟨g⁻¹ * u, ?_, ?_⟩
      · simpa using hu
      · change ((g⁻¹ * u : ℂˣ) : ℂ) = x
        simp only [Units.val_mul]
        rw [he]; simp
  rw [hpre, withDensity_apply _ (by exact (ev.measurableSet_image.mpr hs).preimage (by fun_prop)),
    withDensity_apply _ (ev.measurableSet_image.mpr hs)]
  have hscale := complex_addHaar_map_mul μ (g : ℂ) g.ne_zero
  have hmul (x : ℂ) : D ((g : ℂ) * x) = (ENNReal.ofReal (‖(g : ℂ)‖ ^ 2))⁻¹ * D x := by
    dsimp [D]
    rw [norm_mul, mul_pow, show Real.pi * (‖(g : ℂ)‖ ^ 2 * ‖x‖ ^ 2) =
      ‖(g : ℂ)‖ ^ 2 * (Real.pi * ‖x‖ ^ 2) by ring, mul_inv,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos
        (pow_pos (norm_pos_iff.mpr g.ne_zero) 2)]
  have hm := setLIntegral_map (μ := μ) (g := fun x : ℂ => (g : ℂ) * x)
    (s := Units.val '' s) (ev.measurableSet_image.mpr hs) hD (by fun_prop)
  rw [hscale, Measure.restrict_smul, lintegral_smul_measure] at hm
  simp only [ENNReal.smul_def, smul_eq_mul] at hm
  simp_rw [hmul] at hm
  rw [lintegral_const_mul _ hD] at hm
  exact (ENNReal.mul_right_inj (by simp) (by simp [norm_pos_iff.mpr g.ne_zero])).mp hm.symm

theorem complexUnits_density_isHaarMeasure (μ : Measure ℂ) [μ.IsAddHaarMeasure] :
    (Measure.comap Units.val
      (μ.withDensity (fun x : ℂ => ENNReal.ofReal ((Real.pi * ‖x‖ ^ 2)⁻¹)))).IsHaarMeasure := by
  letI : BorelSpace ℂˣ := ⟨by
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace ℂ) = borel ℂˣ
    rw [(Units.isEmbedding_val₀ (G₀ := ℂ)).eq_induced, borel_comap]
    rfl⟩
  let ev := (IsOpenUnits.isOpenEmbedding_unitsVal (M := ℂ)).measurableEmbedding
  let D := fun x : ℂ => ENNReal.ofReal ((Real.pi * ‖x‖ ^ 2)⁻¹)
  have hD : Measurable D := by dsimp [D]; fun_prop
  letI := complexUnits_density_left μ
  obtain ⟨K, hK, hKmem⟩ := exists_compact_mem_nhds (1 : ℂˣ)
  have hint : (interior K).Nonempty := ⟨1, mem_interior_iff_mem_nhds.mpr hKmem⟩
  apply Measure.isHaarMeasure_of_isCompact_nonempty_interior _ K hK hint
  · rw [ev.comap_apply]
    change (μ.withDensity D) (Units.val '' K) ≠ 0
    apply mt (withDensity_apply_eq_zero (μ := μ) (s := Units.val '' K) hD).mp
    have heq : {x | D x ≠ 0} ∩ (Units.val '' K) = Units.val '' K := by
      apply Set.inter_eq_right.mpr
      rintro x ⟨u, hu, rfl⟩
      exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr (mul_pos Real.pi_pos
        (pow_pos (norm_pos_iff.mpr u.ne_zero) 2)))).ne'
    rw [heq]
    have hpos : 0 < μ (Units.val '' interior K) :=
      (IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _ isOpen_interior).measure_pos μ
        (hint.image _)
    exact (hpos.trans_le (measure_mono (Set.image_mono interior_subset))).ne'
  · rw [ev.comap_apply, withDensity_apply _ ((hK.image Units.continuous_val).measurableSet)]
    have hc : ContinuousOn (fun x : ℂ => (Real.pi * ‖x‖ ^ 2)⁻¹) (Units.val '' K) := by
      apply ContinuousOn.inv₀ (by fun_prop)
      rintro x ⟨u, hu, rfl⟩
      exact (mul_pos Real.pi_pos (pow_pos (norm_pos_iff.mpr u.ne_zero) 2)).ne'
    have hi := ContinuousOn.integrableOn_compact (μ := μ) (hK.image Units.continuous_val) hc
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x => by positivity))]
    exact ENNReal.ofReal_ne_top

theorem schwartz_complexUnitsMellin_integrable_of_isHaarMeasure
    (g : SchwartzMap ℂ ℂ) (ν : Measure ℂˣ) [ν.IsHaarMeasure]
    (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : ℂˣ => g x.val * ((‖x.val‖ ^ 2 : ℝ) : ℂ) ^ z) ν := by
  letI : BorelSpace ℂˣ := ⟨by
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace ℂ) = borel ℂˣ
    rw [(Units.isEmbedding_val₀ (G₀ := ℂ)).eq_induced, borel_comap]
    rfl⟩
  letI : SecondCountableTopology ℂˣ :=
    (Units.isEmbedding_val₀ (G₀ := ℂ)).secondCountableTopology
  let μ₀ : Measure ℂˣ := Measure.comap Units.val
    (volume.withDensity (fun x : ℂ => ENNReal.ofReal ((Real.pi * ‖x‖ ^ 2)⁻¹)))
  letI : μ₀.IsHaarMeasure := complexUnits_density_isHaarMeasure volume
  exact integrable_of_isHaarMeasure μ₀ ν
    (schwartz_complexUnitsMellin_integrable g volume z hz)

theorem fourier_mellin_integrable
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (hne : ∀ v, e v ≠ 1)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (ν : @Measure (SLocalProduct F A.Sf)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (hν : @Measure.IsHaarMeasure (SLocalProduct F A.Sf)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)) ν)
    (W0 : SLocalProduct F A.Sf → ℂ)
    (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (hcompact : HasCompactSupport W0) (hannular : tsupport W0 ⊆ {x | IsUnit x})
    (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun y : (SLocalProduct F A.Sf)ˣ =>
      ProbeWeight.fourier F A.Sf e μ W0 y.val *
        (ProbeWeight.modulus F A.Sf y : ℂ) ^ z) ν := by
  obtain ⟨c, gReal, gComplex, gFinite, hFinite, htensor⟩ :=
    ProbeSheetVerticalDecay.fourier_isSchwartzTensor A.Sf e he hne μ hμ W0 hW0 hcompact
  apply ProbeSheetGlobalIntegrability.tensor_units_mellin_integrable F A.Sf
    (ProbeWeight.fourier F A.Sf e μ W0) c
    (fun v => (gReal v : ℝ → ℂ)) (fun v => (gComplex v : ℂ → ℂ)) gFinite
    htensor z _ _ _ ν hν
  · intro v νv hνv
    letI := hνv
    exact ProbeSheetGlobalIntegrability.schwartz_realUnitsMellin_integrable
      (gReal v) νv z hz
  · intro v νv hνv
    letI := hνv
    exact schwartz_complexUnitsMellin_integrable_of_isHaarMeasure (gComplex v) νv z hz
  · intro v νv hνv
    letI := hνv
    exact ProbeSheetGlobalIntegrability.finiteUnitsMellin_integrable F v.val
      (gFinite v) (hFinite v).1 (hFinite v).2 νv z hz

end
end DedekindZetaZeroFree.ProbeSheetFourierMellinBounds

end
