module

public import DedekindZetaZeroFree.Analysis.Sobolev.Approximation.CompactMollificationBounds
public import DedekindZetaZeroFree.Analysis.Sobolev.Embedding.IteratedCoordinateIntegralBound
public import DedekindZetaZeroFree.Analysis.Sobolev.Embedding.CompactMixedDerivativeBound

@[expose] public section

section

noncomputable section

namespace DedekindZetaZeroFree.KPLocalCubeSobolevJets.Interior

open MeasureTheory KPContLocalNorm Filter Topology
open scoped Convolution

theorem mollify_tendsto_of_continuous {n : ℕ} (f : Space n → ℂ) (hf : Continuous f)
    (φ : Space n → ℝ) (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hunit : (∫ y, φ y) = 1) (δ : ℝ) (x : Space n) :
    Tendsto (fun t : ℕ => mollify φ δ f t x)
      atTop (nhds (f x)) := by
  have hc : Continuous (fun c : ℝ => ∫ y, (φ y : ℂ) * f (x - c • y)) := by
    rw [← continuousOn_univ]
    apply continuousOn_integral_of_compact_support hs.isCompact
    · exact (by fun_prop : Continuous (fun p : ℝ × Space n => (φ p.2 : ℂ) * f (x - p.1 • p.2))).continuousOn
    · intro c y _ hy
      simp [image_eq_zero_of_notMem_tsupport hy]
  have ht : Tendsto (fun t : ℕ => δ / (t + 1 : ℕ)) atTop (nhds (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hz : (∫ y, (φ y : ℂ) * f (x - (0 : ℝ) • y)) = f x := by
    simp only [zero_smul, sub_zero]
    rw [integral_mul_const, integral_complex_ofReal, hunit]
    simp
  simpa only [mollify, hz, Function.comp_def] using
    hc.continuousAt.tendsto.comp ht

theorem mollify_eq_of_ae {n : ℕ} (U : Set (Space n)) (hU : MeasurableSet U)
    (h f : Space n → ℂ) (hh : h =ᵐ[volume.restrict U] f)
    (φ : Space n → ℝ) (δ : ℝ) (t : ℕ) (hc : δ / (t + 1 : ℕ) ≠ 0)
    (x : Space n) (hsub : ∀ y ∈ tsupport φ, x - (δ / (t + 1 : ℕ)) • y ∈ U) :
    mollify φ δ h t x = mollify φ δ f t x := by
  have hq : Measure.QuasiMeasurePreserving (fun y : Space n => x - (δ / (t + 1 : ℕ)) • y)
      volume volume := by
    simpa only [Function.comp_def, sub_eq_add_neg, neg_smul] using
      (measurePreserving_add_left volume x).quasiMeasurePreserving.comp
        ((Measure.quasiMeasurePreserving_smul volume (neg_ne_zero.mpr hc)))
  have he := hq.ae ((ae_restrict_iff' hU).mp hh)
  apply integral_congr_ae
  filter_upwards [he] with y hy
  by_cases hs : y ∈ tsupport φ
  · rw [hy (hsub y hs)]
  · simp [image_eq_zero_of_notMem_tsupport hs]

private theorem coordinateDerivativeList_germ {n : ℕ} (l : List (Fin n))
    {f g : Space n → ℂ} {x : Space n} (hfg : f =ᶠ[nhds x] g) :
    coordinateDerivativeList l f =ᶠ[nhds x] coordinateDerivativeList l g := by
  induction l with
  | nil => exact hfg
  | cons i l ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L => L (EuclideanSpace.single i 1)) hy

theorem mollify_germ_of_ae {n : ℕ} (U : Set (Space n)) (hU : IsOpen U)
    (h f : Space n → ℂ) (hh : h =ᵐ[volume.restrict U] f)
    (φ : Space n → ℝ) (hs : HasCompactSupport φ) (δ : ℝ) (hδ : 0 < δ)
    (x : Space n) (hx : x ∈ U) :
    ∀ᶠ t : ℕ in atTop, mollify φ δ h t =ᶠ[nhds x] mollify φ δ f t := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨R, hR, hbound⟩ := hs.isCompact.isBounded.subset_closedBall_lt 0 (0 : Space n)
  have ht : Tendsto (fun t : ℕ => δ / (t + 1 : ℕ)) atTop (nhds (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have he := (ht.norm.mul_const R).eventually (gt_mem_nhds (show ‖(0 : ℝ)‖ * R < r / 2 by simpa using half_pos hr))
  filter_upwards [he] with t ht
  filter_upwards [Metric.ball_mem_nhds x (half_pos hr)] with z hz
  apply mollify_eq_of_ae U hU.measurableSet h f hh φ δ t
    (div_ne_zero hδ.ne' (by positivity)) z
  intro y hy
  apply hball
  rw [Metric.mem_ball]
  have hb : ‖(δ / (t + 1 : ℕ)) • y‖ < r / 2 := by
    rw [norm_smul]
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) ht
    simpa [Metric.mem_closedBall, dist_eq_norm] using hbound hy
  calc
    dist (z - (δ / (t + 1 : ℕ)) • y) x ≤
        dist (z - (δ / (t + 1 : ℕ)) • y) z + dist z x := dist_triangle _ _ _
    _ < r / 2 + r / 2 := by
      apply add_lt_add _ (Metric.mem_ball.mp hz)
      simpa [dist_eq_norm] using hb
    _ = r := add_halves r

theorem mollify_coordinateDerivative_eq_of_ae {n m : ℕ} (U : Set (Space n)) (hU : IsOpen U)
    (h f : Space n → ℂ) (hh : h =ᵐ[volume.restrict U] f)
    (φ : Space n → ℝ) (hs : HasCompactSupport φ) (δ : ℝ) (hδ : 0 < δ)
    (α : MultiIndex n m) (x : Space n) (hx : x ∈ U) :
    ∀ᶠ t : ℕ in atTop,
      coordinateDerivative α (mollify φ δ h t) x = coordinateDerivative α (mollify φ δ f t) x := by
  filter_upwards [mollify_germ_of_ae U hU h f hh φ hs δ hδ x hx] with t ht
  exact (coordinateDerivativeList_germ α.directions ht).eq_of_nhds

theorem exists_compact_finite_order_extension_germ {n m : ℕ} (U : Set (Space n)) (hU : IsOpen U)
    (f : Space n → ℂ) (hf : ContDiffOn ℝ m f U) (x : Space n) (hx : x ∈ U) :
    ∃ g : Space n → ℂ, ContDiff ℝ m g ∧ HasCompactSupport g ∧ f =ᶠ[nhds x] g := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let χ : ContDiffBump x := ⟨r / 4, r / 2, by linarith, by linarith⟩
  let g : Space n → ℂ := fun y => χ y • f y
  have hsub : tsupport (fun y => χ y) ⊆ U := by
    rw [χ.tsupport_eq]
    intro y hy
    exact hball ((Metric.mem_closedBall.mp hy).trans_lt (by dsimp [χ]; linarith))
  refine ⟨g, ?_, χ.hasCompactSupport.smul_right, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport (fun z => χ z)
    · exact ((χ.contDiff.of_le (show (m : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast le_top)).contDiffAt.smul
        (hf.contDiffAt (hU.mem_nhds (hsub hy))))
    · have hz : g =ᶠ[nhds y] (fun _ => 0) := by
        filter_upwards [isClosed_tsupport (fun z => χ z) |>.isOpen_compl.mem_nhds hy] with z hz
        dsimp [g]
        rw [image_eq_zero_of_notMem_tsupport hz]
        simp
      exact contDiffAt_const.congr_of_eventuallyEq hz
  · filter_upwards [χ.eventuallyEq_one] with y hy
    dsimp [g]
    rw [hy]
    simp

private theorem mollify_eq_scaled_convolution {n : ℕ} (φ : Space n → ℝ) (f : Space n → ℂ)
    (δ : ℝ) (t : ℕ) (hc : δ / (t + 1 : ℕ) ≠ 0) :
    mollify φ δ f t = fun x => |((δ / (t + 1 : ℕ)) ^ Module.finrank ℝ (Space n))⁻¹| •
      ((fun y => φ ((δ / (t + 1 : ℕ))⁻¹ • y)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x := by
  funext x
  let c := δ / (t + 1 : ℕ)
  have he := Measure.integral_comp_smul (volume : Measure (Space n))
    (fun z => (φ (c⁻¹ • z) : ℂ) * f (x - z)) c
  have hi : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  simp only [smul_smul, hi, one_smul] at he
  simpa only [mollify, c, convolution_def, ContinuousLinearMap.lsmul_apply, Complex.real_smul] using he
private theorem coordinateDerivativeList_contDiff_global {n : ℕ} (l : List (Fin n)) (q : ℕ) {f : Space n → ℂ}
    (hf : ContDiff ℝ (q + l.length : ℕ) f) :
    ContDiff ℝ q (coordinateDerivativeList l f) := by
  induction l generalizing q with
  | nil => simpa [coordinateDerivativeList] using hf
  | cons i l ih =>
    have h' : ContDiff ℝ (q + 1 : ℕ) (coordinateDerivativeList l f) := by
      apply ih
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf
    apply h'.fderiv_right ?_ |>.clm_apply contDiff_const
    simp only [Nat.cast_add, Nat.cast_one]
    exact le_rfl
private theorem coordinateDerivativeList_compact_global {n : ℕ} (l : List (Fin n)) {f : Space n → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (coordinateDerivativeList l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact ih.fderiv_apply ℝ _
private theorem coordinateDerivativeList_convolution_global {n : ℕ} (l : List (Fin n)) {f : Space n → ℂ}
    (hf : ContDiff ℝ (l.length : ℕ) f) (hs : HasCompactSupport f)
    (φ : Space n → ℝ) (hφ : Continuous φ) :
    coordinateDerivativeList l (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) =
      φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (coordinateDerivativeList l f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have hf' : ContDiff ℝ (l.length : ℕ) f := hf.of_le (by simp)
    rw [coordinateDerivativeList, ih hf']
    funext x
    have hcd : ContDiff ℝ (1 : ℕ) (coordinateDerivativeList l f) := by
      apply coordinateDerivativeList_contDiff_global l 1
      convert hf using 1 <;> simp [List.length_cons, Nat.add_comm]
    rw [(coordinateDerivativeList_compact_global l hs |>.hasFDerivAt_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hφ.locallyIntegrable (by simpa using hcd) x).fderiv]
    rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hφ.locallyIntegrable
      (coordinateDerivativeList_compact_global l hs |>.fderiv ℝ) (hcd.continuous_fderiv (by simp))]
    rfl
private theorem coordinateDerivativeList_real_smul {n : ℕ} (l : List (Fin n)) (c : ℝ) (f : Space n → ℂ) :
    coordinateDerivativeList l (fun y => c • f y) = fun y => c • coordinateDerivativeList l f y := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [coordinateDerivativeList, ih]
    funext x
    simpa only [Pi.smul_def, Pi.smul_apply, ContinuousLinearMap.smul_apply] using
      congrArg (fun L : Space n →L[ℝ] ℂ => L (EuclideanSpace.single i 1))
        (congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := coordinateDerivativeList l f) c) x)

theorem coordinateDerivativeList_mollify_global {n : ℕ} (l : List (Fin n)) {f : Space n → ℂ}
    (hf : ContDiff ℝ (l.length : ℕ) f) (hs : HasCompactSupport f)
    (φ : Space n → ℝ) (hφ : Continuous φ) (δ : ℝ) (t : ℕ)
    (hc : δ / (t + 1 : ℕ) ≠ 0) :
    coordinateDerivativeList l (mollify φ δ f t) = mollify φ δ (coordinateDerivativeList l f) t := by
  rw [mollify_eq_scaled_convolution φ f δ t hc, coordinateDerivativeList_real_smul,
    coordinateDerivativeList_convolution_global l hf hs _ (by fun_prop), mollify_eq_scaled_convolution φ _ δ t hc]

theorem mollify_finite_jet_tendsto {n m : ℕ} (U : Set (Space n))
    (hU : IsOpen U) (f : Space n → ℂ) (hf : ContDiffOn ℝ m f U)
    (h : Lp ℂ 2 (volume : Measure (Space n)))
    (hh : (fun x => h x) =ᵐ[volume.restrict U] f)
    (φ : Space n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : HasCompactSupport φ) (hunit : (∫ y, φ y) = 1)
    (δ : ℝ) (hδ : 0 < δ) (α : MultiIndex n m) (x : Space n) (hx : x ∈ U) :
    Filter.Tendsto (fun t => coordinateDerivative α (mollify φ δ (fun y => h y) t) x)
      Filter.atTop (nhds (coordinateDerivative α f x)) := by
  obtain ⟨g, hg, hgs, hfg⟩ := exists_compact_finite_order_extension_germ U hU f hf x hx
  obtain ⟨r, hr, heq⟩ := Metric.eventually_nhds_iff.mp hfg
  have hfg' : f =ᵐ[volume.restrict (Metric.ball x r)] g := by
    apply (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr
    exact Filter.Eventually.of_forall (fun y hy => heq (Metric.mem_ball.mp hy))
  have hhg : (fun y => h y) =ᵐ[volume.restrict (U ∩ Metric.ball x r)] g := by
    have hhr := ae_restrict_of_ae_restrict_of_subset (Set.inter_subset_left : U ∩ Metric.ball x r ⊆ U) hh
    have hfr := ae_restrict_of_ae_restrict_of_subset (Set.inter_subset_right : U ∩ Metric.ball x r ⊆ Metric.ball x r) hfg'
    filter_upwards [hhr, hfr] with y hy hy'
    exact hy.trans hy'
  have hlen : α.directions.length ≤ m := by
    have he : α.directions.length = α.degree := by
      simp [MultiIndex.directions, MultiIndex.degree, List.length_flatMap,
        List.finRange, List.sum_ofFn, Function.comp_def]
    rw [he]
    exact α.property
  have hgl : ContDiff ℝ (α.directions.length : ℕ) g := hg.of_le (by exact_mod_cast hlen)
  have hc : Continuous (coordinateDerivative α g) := by
    exact (coordinateDerivativeList_contDiff_global α.directions 0 (by simpa using hgl)).continuous
  have ht := mollify_tendsto_of_continuous (coordinateDerivative α g) hc φ hφ.continuous hs hunit δ x
  have hj : coordinateDerivative α f x = coordinateDerivative α g x :=
    (coordinateDerivativeList_germ α.directions hfg).eq_of_nhds
  have he := mollify_coordinateDerivative_eq_of_ae (U ∩ Metric.ball x r)
    (hU.inter Metric.isOpen_ball) (fun y => h y) g hhg φ hs δ hδ α x
    ⟨hx, Metric.mem_ball_self hr⟩
  have he' : (fun t => coordinateDerivative α (mollify φ δ (fun y => h y) t) x) =ᶠ[atTop]
      (fun t => mollify φ δ (coordinateDerivative α g) t x) := by
    filter_upwards [he] with t ht
    rw [ht]
    exact congrFun (coordinateDerivativeList_mollify_global α.directions hgl hgs φ hφ.continuous δ t
      (div_ne_zero hδ.ne' (by positivity))) x
  simpa only [hj] using ht.congr' he'.symm

end DedekindZetaZeroFree.KPLocalCubeSobolevJets.Interior

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPLocalCubeSobolevJets

open MeasureTheory KPContLocalNorm
open scoped ContDiff

 theorem coordinateDerivativeList_contDiffOn_finite {n : ℕ}
    {U : Set (Space n)} (hU : IsOpen U) (l : List (Fin n)) (q : ℕ)
    {f : Space n → ℂ} (hf : ContDiffOn ℝ (q + l.length) f U) :
    ContDiffOn ℝ q (coordinateDerivativeList l f) U := by
  induction l generalizing q with
  | nil => simpa [coordinateDerivativeList] using hf
  | cons i l ih =>
    have ht : ContDiffOn ℝ ((q + 1) + l.length) f U := by
      convert hf using 1 <;> simp [add_assoc, add_comm, add_left_comm]
    have hd := (ih (q + 1) ht).fderiv_of_isOpen hU (m := (q : ℕ∞ω)) (by simp)
    exact hd.clm_apply contDiffOn_const

 theorem multiIndex_directions_length {n k : ℕ} (α : MultiIndex n k) :
    α.directions.length = α.degree := by
  simp [MultiIndex.directions, MultiIndex.degree, List.length_flatMap,
    List.finRange, List.sum_ofFn, Function.comp_def]

 theorem coordinateDerivative_continuousOn_finite {n m : ℕ}
    {U : Set (Space n)} (hU : IsOpen U) {f : Space n → ℂ}
    (hf : ContDiffOn ℝ m f U) (α : MultiIndex n m) :
    ContinuousOn (coordinateDerivative α f) U := by
  have hlen : α.directions.length ≤ m := by
    rw [multiIndex_directions_length]
    exact α.property
  have hle : (0 : ℕ∞ω) + (α.directions.length : ℕ∞ω) ≤ (m : ℕ∞ω) := by
    simpa using (ENat.coe_le_coe.mpr hlen)
  have hd := coordinateDerivativeList_contDiffOn_finite hU α.directions 0
    (hf.of_le hle)
  exact hd.continuousOn

def finiteCompactJet {n m : ℕ} (B : LocalBall n) (K : Set (Space n))
    (hK : K ⊆ B.carrier) (f : Space n → ℂ)
    (hf : ContDiffOn ℝ m f B.carrier) : CompactJets K m :=
  fun α => ⟨fun x => coordinateDerivative α f x,
    ((coordinateDerivative_continuousOn_finite Metric.isOpen_ball hf α).mono hK).restrict⟩

@[simp] theorem finiteCompactJet_apply {n m : ℕ} (B : LocalBall n)
    (K : Set (Space n)) (hK : K ⊆ B.carrier) (f : Space n → ℂ)
    (hf : ContDiffOn ℝ m f B.carrier) (α : MultiIndex n m) (x : K) :
    finiteCompactJet B K hK f hf α x = coordinateDerivative α f x := rfl

theorem jetMaxNorm_le_iff {n m : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (j : CompactJets K m) {R : ℝ} (hR : 0 ≤ R) :
    jetMaxNorm hK j ≤ R ↔ ∀ α : MultiIndex n m, ∀ x : K, ‖j α x‖ ≤ R := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  change ‖j‖ ≤ R ↔ _
  rw [pi_norm_le_iff_of_nonneg hR]
  exact forall_congr' (fun α => ContinuousMap.norm_le (j α) hR)

theorem finite_order_representative_interior_jet_exists {n : ℕ}
    (A B : LocalBall n)
    (hAB : Metric.closedBall A.center A.radius ⊆ B.carrier) (m : ℕ)
    (f : Space n → ℂ) (hf : ContDiffOn ℝ m f B.carrier) :
    ∃ j : CompactJets (Metric.closedBall A.center A.radius) m,
      ∀ α : MultiIndex n m, ∀ x : Metric.closedBall A.center A.radius,
        j α x = coordinateDerivative α f x := by
  exact ⟨finiteCompactJet B _ hAB f hf, fun _ _ => rfl⟩

theorem coordinateDerivativeList_eventuallyEq {n : ℕ} (l : List (Fin n))
    {f g : Space n → ℂ} {x : Space n} (hfg : f =ᶠ[nhds x] g) :
    coordinateDerivativeList l f =ᶠ[nhds x] coordinateDerivativeList l g := by
  induction l with
  | nil => exact hfg
  | cons i l ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L => L (EuclideanSpace.single i 1)) hy

theorem coordinateDerivative_eqOn_of_ae_representatives {n k m : ℕ}
    (B : LocalBall n) (u : IntegerSobolev B k) (f g : Space n → ℂ)
    (hf : ContinuousOn f B.carrier) (hg : ContinuousOn g B.carrier)
    (hfu : f =ᵐ[volume.restrict B.carrier]
      (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x))
    (hgu : g =ᵐ[volume.restrict B.carrier]
      (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x))
    (α : MultiIndex n m) :
    Set.EqOn (coordinateDerivative α f) (coordinateDerivative α g) B.carrier := by
  have hfg := Measure.eqOn_open_of_ae_eq (hfu.trans hgu.symm)
    (show IsOpen B.carrier from Metric.isOpen_ball) hf hg
  intro x hx
  have hnear : f =ᶠ[nhds x] g := by
    filter_upwards [(show IsOpen B.carrier from Metric.isOpen_ball).mem_nhds hx] with y hy
    exact hfg hy
  exact (coordinateDerivativeList_eventuallyEq α.directions hnear).eq_of_nhds

theorem exists_smooth_interior_cutoff {n : ℕ} (A B : LocalBall n)
    (hAB : Metric.closedBall A.center A.radius ⊆ B.carrier) :
    ∃ χ : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ B.carrier ∧ Set.range χ ⊆ Set.Icc 0 1 ∧
      ∀ x ∈ Metric.closedBall A.center A.radius, χ =ᶠ[nhds x] (fun _ => 1) := by
  let K := Metric.closedBall A.center A.radius
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨δ, hδ, hδB⟩ := hK.exists_cthickening_subset_open Metric.isOpen_ball hAB
  have hsub : Metric.cthickening (δ / 2) K ⊆ Metric.thickening δ K :=
    Metric.cthickening_subset_thickening' hδ (by linarith) K
  obtain ⟨χ, hχ, hrange, hsupp, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
      Metric.isOpen_thickening Metric.isClosed_cthickening hsub
  have hχsub : tsupport χ ⊆ Metric.cthickening δ K := by
    rw [tsupport, hsupp]
    exact Metric.closure_thickening_subset_cthickening δ K
  refine ⟨χ, hχ, hK.cthickening.of_isClosed_subset (isClosed_tsupport χ) hχsub,
    hχsub.trans hδB, hrange, ?_⟩
  intro x hx
  have hx' : x ∈ Metric.thickening (δ / 2) K :=
    Metric.self_subset_thickening (by linarith) K hx
  filter_upwards [Metric.isOpen_thickening.mem_nhds hx'] with y hy
  exact (hone y).mp (Metric.thickening_subset_cthickening (δ / 2) K hy)

theorem smooth_compact_coordinateDerivative {n k : ℕ} (α : MultiIndex n k)
    (w : Space n → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hs : HasCompactSupport w) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative α w) ∧
      HasCompactSupport (coordinateDerivative α w) := by
  have h : ∀ l : List (Fin n),
      ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivativeList l w) ∧
        HasCompactSupport (coordinateDerivativeList l w) := by
    intro l
    induction l with
    | nil => exact ⟨hw, hs⟩
    | cons i l ih =>
      refine ⟨?_, ?_⟩
      · exact ih.1.fderiv_right (by simp) |>.clm_apply contDiff_const
      · exact ih.2.fderiv_apply ℝ _
  exact h α.directions

theorem compact_support_pointwise_jet_bound {n : ℕ} (hn : 0 < n)
    (lower upper : Fin n → ℝ) (hbox : ∀ i, lower i < upper i) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : Space n → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w →
      tsupport w ⊆ {x | ∀ i, lower i < x i ∧ x i < upper i} →
      ∀ (α : MultiIndex n m) (x : Space n),
        ‖coordinateDerivative α w x‖ ≤
          C * Real.sqrt (∑ β : MultiIndex n (m + n),
            ∫ y, ‖coordinateDerivative β w y‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := full_mixed_integral_le_sobolev hn lower upper hbox m
  refine ⟨C, hC, ?_⟩
  intro w hw hs hsub α x
  obtain ⟨hd, hdcomp⟩ := smooth_compact_coordinateDerivative α w hw hs
  exact (norm_le_integral_full_mixed_derivative hn _ hd hdcomp x).trans
    (hbound w hw hs hsub α)

theorem finite_order_jet_bound_of_smooth_approximation {n : ℕ}
    (A B : LocalBall n)
    (hAB : Metric.closedBall A.center A.radius ⊆ B.carrier) (m : ℕ)
    (lower upper : Fin n → ℝ) (hbox : ∀ i, lower i < upper i) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Space n → ℂ)
      (hf : ContDiffOn ℝ m f B.carrier) (R : ℝ), 0 ≤ R →
      ∀ (w : ℕ → Space n → ℂ),
        (∀ t, ContDiff ℝ (⊤ : ℕ∞) (w t)) →
        (∀ t, HasCompactSupport (w t)) →
        (∀ t, tsupport (w t) ⊆
          {x | ∀ i, lower i < x i ∧ x i < upper i}) →
        (∀ t, Real.sqrt (∑ β : MultiIndex n (m + n),
          ∫ y, ‖coordinateDerivative β (w t) y‖ ^ 2) ≤ R) →
        (∀ (α : MultiIndex n m) (x : Metric.closedBall A.center A.radius),
          Filter.Tendsto (fun t => coordinateDerivative α (w t) x)
            Filter.atTop (nhds (coordinateDerivative α f x))) →
        ∃ j : CompactJets (Metric.closedBall A.center A.radius) m,
          (∀ α : MultiIndex n m, ∀ x : Metric.closedBall A.center A.radius,
            j α x = coordinateDerivative α f x) ∧
          jetMaxNorm (isCompact_closedBall A.center A.radius) j ≤ C * R := by
  obtain ⟨C, hC, hbound⟩ := compact_support_pointwise_jet_bound
    A.dimension_pos lower upper hbox m
  refine ⟨C, hC, ?_⟩
  intro f hf R hR w hw hs hsub hnorm hlim
  refine ⟨finiteCompactJet B _ hAB f hf, (fun _ _ => rfl), ?_⟩
  apply (jetMaxNorm_le_iff (isCompact_closedBall A.center A.radius) _
    (mul_nonneg hC.le hR)).mpr
  intro α x
  exact le_of_tendsto' (hlim α x).norm (fun t =>
    (hbound (w t) (hw t) (hs t) (hsub t) α x).trans
      (mul_le_mul_of_nonneg_left (hnorm t) hC.le))

theorem coordinateDerivativeList_zero {n : ℕ} (l : List (Fin n)) :
    coordinateDerivativeList l (fun _ : Space n => (0 : ℂ)) = fun _ => 0 := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [coordinateDerivativeList, ih]

theorem sobolevNorm_zero_derivative {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (hu : u.sobolevNorm = 0) (α : MultiIndex n k) :
    u.derivatives α = 0 := by
  have hs : u.normSq = 0 := by rw [← u.sobolevNorm_sq, hu]; simp
  have hα : ‖u.derivatives α‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun β _ => sq_nonneg ‖u.derivatives β‖)).mp hs α
      (Finset.mem_univ α)
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (u.derivatives α)])

theorem finite_order_representative_zero_norm {n : ℕ}
    (A B : LocalBall n)
    (hAB : Metric.closedBall A.center A.radius ⊆ B.carrier) (m : ℕ)
    (u : IntegerSobolev B (m + n)) (hu : u.sobolevNorm = 0)
    (f : Space n → ℂ) (hf : ContDiffOn ℝ m f B.carrier)
    (hfu : f =ᵐ[volume.restrict B.carrier]
      (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n (m+n)) x)) :
    ∃ j : CompactJets (Metric.closedBall A.center A.radius) m,
      (∀ α : MultiIndex n m, ∀ x : Metric.closedBall A.center A.radius,
        j α x = coordinateDerivative α f x) ∧
      jetMaxNorm (isCompact_closedBall A.center A.radius) j = 0 := by
  have hzero : (fun _ : Space n => (0 : ℂ)) =ᵐ[volume.restrict B.carrier]
      (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n (m+n)) x) := by
    rw [sobolevNorm_zero_derivative u hu]
    exact (Lp.coeFn_zero ℂ 2 (volume.restrict B.carrier)).symm
  have hd := coordinateDerivative_eqOn_of_ae_representatives (m := m) B u f (fun _ => 0)
    hf.continuousOn continuousOn_const hfu hzero
  refine ⟨finiteCompactJet B _ hAB f hf, (fun _ _ => rfl), ?_⟩
  apply le_antisymm
  · apply (jetMaxNorm_le_iff (isCompact_closedBall A.center A.radius) _ le_rfl).mpr
    intro α x
    rw [finiteCompactJet_apply, hd α (hAB x.property)]
    simp [coordinateDerivative, coordinateDerivativeList_zero]
  · exact norm_nonneg _

theorem finite_order_representative_interior_jet_bound_of_approximation {n : ℕ}
    (A B : LocalBall n)
    (hAB : Metric.closedBall A.center A.radius ⊆ B.carrier) (m : ℕ)
    (lower upper : Fin n → ℝ) (hbox : ∀ i, lower i < upper i)
    (D : ℝ) (hD : 0 < D)
    (happrox : ∀ (u : IntegerSobolev B (m + n)) (f : Space n → ℂ),
      ContDiffOn ℝ m f B.carrier →
      (f =ᵐ[volume.restrict B.carrier]
        (fun x => u.derivatives
          (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x)) →
      ∃ w : ℕ → Space n → ℂ,
        (∀ t, ContDiff ℝ (⊤ : ℕ∞) (w t)) ∧
        (∀ t, HasCompactSupport (w t)) ∧
        (∀ t, tsupport (w t) ⊆
          {x | ∀ i, lower i < x i ∧ x i < upper i}) ∧
        (∀ t, Real.sqrt (∑ β : MultiIndex n (m + n),
          ∫ y, ‖coordinateDerivative β (w t) y‖ ^ 2) ≤ D * u.sobolevNorm) ∧
        (∀ (α : MultiIndex n m) (x : Metric.closedBall A.center A.radius),
          Filter.Tendsto (fun t => coordinateDerivative α (w t) x)
            Filter.atTop (nhds (coordinateDerivative α f x)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : IntegerSobolev B (m + n)) (f : Space n → ℂ),
      ContDiffOn ℝ m f B.carrier →
      (f =ᵐ[volume.restrict B.carrier]
        (fun x => u.derivatives
          (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x)) →
      ∃ j : CompactJets (Metric.closedBall A.center A.radius) m,
        (∀ α : MultiIndex n m, ∀ x : Metric.closedBall A.center A.radius,
          j α x = coordinateDerivative α f x) ∧
        jetMaxNorm (isCompact_closedBall A.center A.radius) j ≤ C * u.sobolevNorm := by
  obtain ⟨C, hC, hbound⟩ := finite_order_jet_bound_of_smooth_approximation
    A B hAB m lower upper hbox
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro u f hf hfu
  obtain ⟨w, hw, hs, hsub, hnorm, hlim⟩ := happrox u f hf hfu
  simpa only [mul_assoc] using hbound f hf (D * u.sobolevNorm)
    (mul_nonneg hD.le (Real.sqrt_nonneg _)) w hw hs hsub hnorm hlim

theorem finite_order_representative_interior_jet_bound {n : ℕ}
    (A B : LocalBall n)
    (hAB : Metric.closedBall A.center A.radius ⊆ B.carrier) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : IntegerSobolev B (m + n)) (f : Space n → ℂ),
      ContDiffOn ℝ m f B.carrier →
      (f =ᵐ[volume.restrict B.carrier]
        (fun x => u.derivatives
          (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x)) →
      ∃ j : CompactJets (Metric.closedBall A.center A.radius) m,
        (∀ α : MultiIndex n m, ∀ x : Metric.closedBall A.center A.radius,
          j α x = coordinateDerivative α f x) ∧
        jetMaxNorm (isCompact_closedBall A.center A.radius) j ≤ C * u.sobolevNorm := by
  obtain ⟨χ, hχ, hsχ, hχB, _, hone⟩ := exists_smooth_interior_cutoff A B hAB
  obtain ⟨L, hL, hloc⟩ := Interior.cutoff_global_weak_sobolev B (m + n) χ hχ hsχ hχB
  obtain ⟨lower, upper, hbox, δ, hδ, φ, hφ, hsφ, _, _, hunit, hmoll⟩ :=
    Interior.compact_weak_mollification_on_box A.dimension_pos (m + n)
      (tsupport χ) hsχ
  obtain ⟨C, hC, htransfer⟩ :=
    finite_order_jet_bound_of_smooth_approximation A B hAB m lower upper hbox
  refine ⟨C * L, mul_pos hC hL, ?_⟩
  intro u f hf hfu
  obtain ⟨g, hzero, hsupport, hnorm⟩ := hloc u
  let w := fun t => Interior.mollify φ δ
    (fun x => g.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x) t
  have hwt := hmoll g hsupport
  have hlim : ∀ (α : MultiIndex n m) (x : Metric.closedBall A.center A.radius),
      Filter.Tendsto (fun t => coordinateDerivative α (w t) x)
        Filter.atTop (nhds (coordinateDerivative α f x)) := by
    intro α x
    obtain ⟨V, hVχ, hV, hxV⟩ := eventually_nhds_iff.mp (hone x x.property)
    let U := V ∩ B.carrier
    have hU : IsOpen U := hV.inter Metric.isOpen_ball
    have hUB : U ⊆ B.carrier := Set.inter_subset_right
    have hxU : (x : Space n) ∈ U := ⟨hxV, hAB x.property⟩
    have heq : (fun y => g.derivatives
        (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) y)
        =ᵐ[volume.restrict U] f := by
      filter_upwards [ae_restrict_of_ae hzero,
        ae_restrict_of_ae_restrict_of_subset hUB hfu,
        ae_restrict_mem hU.measurableSet] with y hgy hfy hy
      rw [hgy, Set.indicator_of_mem (hUB hy), hVχ y hy.1, one_smul, ← hfy]
    exact Interior.mollify_finite_jet_tendsto U hU f (hf.mono hUB)
      (g.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)))
      heq φ hφ hsφ hunit δ hδ α x hxU
  have hR : 0 ≤ L * u.sobolevNorm := mul_nonneg hL.le (Real.sqrt_nonneg _)
  obtain ⟨j, hj, hbound⟩ := htransfer f hf (L * u.sobolevNorm) hR w
    (fun t => (hwt t).1) (fun t => (hwt t).2.1) (fun t => (hwt t).2.2.1)
    (fun t => (hwt t).2.2.2.trans hnorm) hlim
  exact ⟨j, hj, by simpa only [mul_assoc] using hbound⟩

end DedekindZetaZeroFree.KPLocalCubeSobolevJets

end

end
