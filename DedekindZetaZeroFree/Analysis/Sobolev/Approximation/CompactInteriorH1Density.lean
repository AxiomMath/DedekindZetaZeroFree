module

public import DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.WeakSolutions

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates

open MeasureTheory KPContLocalNorm Raw Filter Topology

namespace CompactApproximation

open scoped Convolution Pointwise

def compactZeroExtension {n : ℕ} {B : LocalBall n} (K : Set (Space n))
    (f : BallL2 B) : Space n → ℂ := K.indicator (fun x => f x)

theorem compactZeroExtension_memLp {n : ℕ} {B : LocalBall n}
    {K : Set (Space n)} (hK : IsCompact K) (hKB : K ⊆ B.carrier) (f : BallL2 B) :
    MemLp (compactZeroExtension K f) 2 volume := by
  apply (memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet).2
  exact (Lp.memLp f).mono_measure (Measure.restrict_mono hKB le_rfl)

theorem compactZeroExtension_ae {n : ℕ} {B : LocalBall n}
    {K : Set (Space n)} (f : BallL2 B)
    (hf : ∀ᵐ x ∂volume.restrict B.carrier, x ∉ K → f x = 0) :
    compactZeroExtension K f =ᵐ[volume.restrict B.carrier] fun x => f x := by
  filter_upwards [hf] with x hx
  by_cases h : x ∈ K
  · simp [compactZeroExtension, h]
  · simp [compactZeroExtension, h, hx h]

theorem compactZeroExtension_tsupport {n : ℕ} {B : LocalBall n}
    {K : Set (Space n)} (hK : IsCompact K) (f : BallL2 B) :
    tsupport (compactZeroExtension K f) ⊆ K := by
  exact closure_minimal Set.support_indicator_subset hK.isClosed

theorem compactZeroExtension_hasCompactSupport {n : ℕ} {B : LocalBall n}
    {K : Set (Space n)} (hK : IsCompact K) (f : BallL2 B) :
    HasCompactSupport (compactZeroExtension K f) :=
  hK.of_isClosed_subset isClosed_closure (compactZeroExtension_tsupport hK f)

theorem convolution_tsupport_subset_thickening {n : ℕ}
    (φ : ContDiffBump (0 : Space n)) {g : Space n → ℂ}
    {K : Set (Space n)} (hK : IsCompact K) (hg : tsupport g ⊆ K)
    {δ : ℝ} (hδ : φ.rOut ≤ δ) :
    tsupport (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) ⊆
      Metric.cthickening δ K := by
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  have hs := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hx
  rcases Set.mem_add.mp hs with ⟨a, ha, b, hb, rfl⟩
  have ha' : ‖a‖ ≤ δ := by
    rw [φ.support_normed_eq, Metric.mem_ball, dist_zero_right] at ha
    exact ha.le.trans hδ
  apply Metric.mem_cthickening_of_dist_le (a + b) b δ K (hg (subset_closure hb))
  simpa [dist_eq_norm] using ha'

def mollifiedTest {n : ℕ} {B : LocalBall n} {K : Set (Space n)}
    (hK : IsCompact K) (hKB : K ⊆ B.carrier) (f : BallL2 B)
    (φ : ContDiffBump (0 : Space n)) {δ : ℝ} (hδ : φ.rOut ≤ δ)
    (hδB : Metric.cthickening δ K ⊆ B.carrier) : TestFunction B.toOpens ℂ ⊤ := by
  let g := compactZeroExtension K f
  refine ⟨φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g, ?_, ?_, ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      ((compactZeroExtension_memLp hK hKB f).locallyIntegrable (by norm_num))
  · exact φ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ)
      (compactZeroExtension_hasCompactSupport hK f)
  · exact (convolution_tsupport_subset_thickening φ hK
      (compactZeroExtension_tsupport hK f) hδ).trans hδB

theorem integral_norm_sq_sub_eq {n : ℕ} (B : LocalBall n)
    (g : Space n → ℂ) (hg : MemLp g 2 (volume.restrict B.carrier))
    (f : BallL2 B) :
    (∫ x in B.carrier, ‖g x - f x‖ ^ 2) = ‖hg.toLp g - f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hg.toLp g) f, hg.coeFn_toLp] with x hx hgx
  simp only [Pi.sub_apply] at hx
  rw [hx, hgx]

theorem integral_norm_sq_sub_tendsto {n : ℕ} (B : LocalBall n)
    (g : ℕ → Space n → ℂ) (hg : ∀ m, MemLp (g m) 2 (volume.restrict B.carrier))
    (f : BallL2 B) (h : Tendsto (fun m => (hg m).toLp (g m)) atTop (𝓝 f)) :
    Tendsto (fun m => ∫ x in B.carrier, ‖g m x - f x‖ ^ 2) atTop (𝓝 0) := by
  simp_rw [integral_norm_sq_sub_eq B _ (hg _) f]
  simpa using (h.sub (tendsto_const_nhds (x := f))).norm.pow 2

def shrinkingBump {n : ℕ} (δ : ℝ) (hδ : 0 < δ) (m : ℕ) :
    ContDiffBump (0 : Space n) :=
  ⟨(δ / (m + 1 : ℝ)) / 2, δ / (m + 1 : ℝ),
    half_pos (div_pos hδ (by positivity)),
    half_lt_self (div_pos hδ (by positivity))⟩

theorem shrinkingBump_rOut_le {n : ℕ} (δ : ℝ) (hδ : 0 < δ) (m : ℕ) :
    (shrinkingBump (n := n) δ hδ m).rOut ≤ δ := by
  change δ / (m + 1 : ℝ) ≤ δ
  exact div_le_self hδ.le (by have := Nat.cast_nonneg (α := ℝ) m; linarith)

theorem shrinkingBump_rOut_tendsto {n : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun m => (shrinkingBump (n := n) δ hδ m).rOut) atTop (𝓝 0) := by
  change Tendsto (fun m : ℕ => δ / (m + 1 : ℝ)) atTop (𝓝 0)
  exact (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).const_div_atTop δ

theorem exists_mollifiedTest_ae_tendsto {n : ℕ} (B : LocalBall n)
    (f : BallL2 B) (K : Set (Space n)) (hK : IsCompact K) (hKB : K ⊆ B.carrier)
    (hf : ∀ᵐ x ∂volume.restrict B.carrier, x ∉ K → f x = 0) :
    ∃ ψ : ℕ → TestFunction B.toOpens ℂ ⊤,
      ∀ᵐ x ∂volume.restrict B.carrier,
        Tendsto (fun m => ψ m x) atTop (𝓝 (f x)) := by
  obtain ⟨δ, hδ, hδB⟩ := hK.exists_cthickening_subset_open Metric.isOpen_ball hKB
  let ψ : ℕ → TestFunction B.toOpens ℂ ⊤ := fun m =>
    mollifiedTest hK hKB f (shrinkingBump δ hδ m)
      (shrinkingBump_rOut_le δ hδ m) hδB
  refine ⟨ψ, ?_⟩
  have hc := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure (Space n))) (φ := shrinkingBump δ hδ)
    (K := 2) (shrinkingBump_rOut_tendsto δ hδ)
    (Eventually.of_forall (fun m => by
      change δ / (m + 1 : ℝ) ≤ 2 * (δ / (m + 1 : ℝ) / 2)
      linarith)) ((compactZeroExtension_memLp hK hKB f).locallyIntegrable (by norm_num))
  filter_upwards [ae_restrict_of_ae hc, compactZeroExtension_ae f hf] with x hx heq
  change Tendsto (fun m =>
    (ContDiffBump.normed (shrinkingBump δ hδ m) volume
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] compactZeroExtension K f) x)
    atTop (𝓝 (f x))
  rw [heq] at hx
  exact hx

def translateL2 {n : ℕ} (f : Lp ℂ 2 (volume : Measure (Space n))) (t : Space n) :
    Lp ℂ 2 (volume : Measure (Space n)) :=
  Lp.compMeasurePreserving (fun x => x - t) (measurePreserving_sub_right volume t) f

 theorem translateL2_continuous {n : ℕ} (f : Lp ℂ 2 (volume : Measure (Space n))) :
    Continuous (translateL2 f) := by
  let g : Space n → C(Space n, Space n) := fun t => ⟨fun x => x - t, by fun_prop⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : Space n × Space n => p.2 - p.1)
    fun_prop
  exact continuous_const.compMeasurePreservingLp hg
    (fun t => measurePreserving_sub_right volume t) (by norm_num)

@[simp] theorem translateL2_zero {n : ℕ} (f : Lp ℂ 2 (volume : Measure (Space n))) :
    translateL2 f 0 = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume (0 : Space n))] with x hx
  simpa [translateL2] using hx

 theorem translateL2_norm {n : ℕ} (f : Lp ℂ 2 (volume : Measure (Space n))) (t : Space n) :
    ‖translateL2 f t‖ = ‖f‖ := by
  exact Lp.norm_compMeasurePreserving f (measurePreserving_sub_right volume t)

 theorem averaged_translateL2_tendsto {n : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Space n)))
    (φ : ℕ → ContDiffBump (0 : Space n))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ t, (φ m).normed volume t • translateL2 f t) atTop (𝓝 f) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure (Space n))) hφ
    ((translateL2_continuous f).comp continuous_neg) (0 : Space n)
  simpa [convolution_def, ContinuousLinearMap.lsmul_apply] using h

theorem coordinateDerivativeList_singleton_mollification {n : ℕ}
    (φ : ContDiffBump (0 : Space n)) (g : Space n → ℂ)
    (hg : LocallyIntegrable g volume) (i : Fin n) (x : Space n) :
    coordinateDerivativeList [i]
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x =
      ((fun y => fderiv ℝ (φ.normed volume) y (EuclideanSpace.single i 1))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (φ.normed volume) := φ.contDiff_normed
  simp only [coordinateDerivativeList]
  rw [(φ.hasCompactSupport_normed.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (hs.of_le (by simp)) hg x).fderiv]
  unfold convolution
  have hi := (φ.hasCompactSupport_normed.fderiv ℝ).convolutionExists_left
    (ContinuousLinearMap.precompL (Space n) (ContinuousLinearMap.lsmul ℝ ℝ))
    (hs.fderiv_right (m := (1 : ℕ∞)) (by simp)).continuous hg x
  rw [ContinuousLinearMap.integral_apply hi]
  simp only [ContinuousLinearMap.precompL_apply]

theorem bounded_continuous_mollification_integral_tendsto {n : ℕ} (B : LocalBall n)
    (g : Space n → ℂ) (hg : Continuous g) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖g x‖ ≤ C) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun m => ∫ x in B.carrier,
      ‖(ContDiffBump.normed (shrinkingBump δ hδ m) volume
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x‖ ^ 2)
      atTop (𝓝 0) := by
  let c := fun m => ContDiffBump.normed (shrinkingBump (n := n) δ hδ m) volume
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  have hc : ∀ m, Continuous (c m) := fun m =>
    (shrinkingBump δ hδ m).hasCompactSupport_normed.continuous_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) ((shrinkingBump δ hδ m).contDiff_normed (n := (⊤ : ℕ∞))).continuous
      hg.locallyIntegrable
  have hf : ∀ x, Tendsto (fun m => c m x) atTop (𝓝 (g x)) := fun x =>
    ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := (volume : Measure (Space n)))
      (shrinkingBump_rOut_tendsto δ hδ) hg x
  have hcbound : ∀ m x, ‖c m x - g x‖ ≤ 2 * C := by
    intro m x
    rw [← dist_eq_norm]
    apply (shrinkingBump δ hδ m).dist_normed_convolution_le hg.aestronglyMeasurable
    intro y hy
    calc dist (g y) (g x) ≤ ‖g y‖ + ‖g x‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * C := by linarith [hbound y, hbound x]
  have hm : volume B.carrier < ⊤ :=
    (Metric.isBounded_ball (x := B.center) (r := B.radius)).measure_lt_top
  letI : IsFiniteMeasure (volume.restrict B.carrier) := ⟨by simpa using hm⟩
  have ht := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict B.carrier) (f := fun _ => (0 : ℝ))
    (fun _ => (2 * C) ^ 2)
    (fun m => (((hc m).sub hg).norm.pow 2).aestronglyMeasurable)
    (integrable_const _) (fun m => Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hcbound m x) 2))
    (Eventually.of_forall (fun x => by
      simpa using ((hf x).sub (tendsto_const_nhds (x := g x))).norm.pow 2))
  simpa only [integral_zero, Pi.sub_apply, Pi.pow_apply, Function.comp_apply] using ht
private theorem derivative_support {n : ℕ} (l : List (Fin n)) (f : Space n → ℂ) :
    tsupport (coordinateDerivativeList l f) ⊆ tsupport f := by
  induction l with
  | nil => exact Set.Subset.rfl
  | cons i l ih =>
      exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans ih

theorem weak_derivatives_zero_off_compact {n : ℕ} (B : LocalBall n)
    (w : IntegerSobolev B 1) (K : Set (Space n)) (hK : IsCompact K)
    (hw : ∀ᵐ x ∂volume.restrict B.carrier, x ∉ K → value w x = 0)
    (α : MultiIndex n 1) :
    ∀ᵐ x ∂volume.restrict B.carrier, x ∉ K → w.derivatives α x = 0 := by
  have hopen : IsOpen (B.carrier \ K) := Metric.isOpen_ball.sdiff hK.isClosed
  have h := hopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume.restrict B.carrier) (f := fun x => w.derivatives α x)
    (((Lp.memLp (w.derivatives α)).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
  have heq : ∀ g : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ B.carrier \ K →
      (∫ x in B.carrier, g x • w.derivatives α x) = 0 := by
    intro g hg hgc hgs
    have hcast : ContDiff ℝ (⊤ : ℕ∞) (fun x => (g x : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hg
    have hsupp : tsupport (fun x => (g x : ℂ)) = tsupport g := by
      unfold tsupport
      congr 1
      ext x
      simp
    let ψ : TestFunction B.toOpens ℂ ⊤ :=
      ⟨fun x => (g x : ℂ), hcast, by change IsCompact _; rw [hsupp]; exact hgc, fun x hx => (hgs (hsupp ▸ hx)).1⟩
    have hweak := w.weak_derivatives α ψ
    have hleft : (∫ x in B.carrier,
        value w x * coordinateDerivative α (fun y => ψ y) x) = 0 := by
      apply integral_eq_zero_of_ae
      change ∀ᵐ x ∂volume.restrict B.carrier, _ = 0
      filter_upwards [hw] with x hx
      by_cases hxK : x ∈ K
      · have hxnot : x ∉ tsupport (coordinateDerivative α (fun y => ψ y)) := by
          intro hh
          have hh' := hgs (hsupp ▸ derivative_support α.directions (fun y => ψ y) hh)
          exact hh'.2 hxK
        rw [image_eq_zero_of_notMem_tsupport hxnot, mul_zero]
      · rw [hx hxK, zero_mul]
    change (∫ x in B.carrier, value w x * coordinateDerivative α (fun y => ψ y) x) =
      (-1 : ℂ) ^ α.degree * (∫ x in B.carrier, w.derivatives α x * (g x : ℂ)) at hweak
    rw [hleft] at hweak
    have hr : (∫ x in B.carrier, w.derivatives α x * (g x : ℂ)) = 0 :=
      (mul_eq_zero.mp hweak.symm).resolve_left (pow_ne_zero _ (by norm_num))
    simpa only [Complex.real_smul, mul_comm] using hr
  have ha := h heq
  filter_upwards [ha, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxB
  exact fun hxK => hx ⟨hxB, hxK⟩
private theorem coordinateDerivativeList_congr_nhds {n : ℕ} (l : List (Fin n))
    {f g : Space n → ℂ} {x : Space n} (h : f =ᶠ[𝓝 x] g) :
    coordinateDerivativeList l f =ᶠ[𝓝 x] coordinateDerivativeList l g := by
  induction l with
  | nil => exact h
  | cons i l ih =>
      filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
      exact congrArg (fun L => L (EuclideanSpace.single i 1)) hy

private theorem integral_compactZeroExtension_mul {n : ℕ} {B : LocalBall n}
    {K : Set (Space n)} (hK : IsCompact K) (hKB : K ⊆ B.carrier)
    (f : BallL2 B) (hf : ∀ᵐ x ∂volume.restrict B.carrier, x ∉ K → f x = 0)
    (g : Space n → ℂ) :
    (∫ x, compactZeroExtension K f x * g x) = ∫ x in B.carrier, f x * g x := by
  have hglobal : (∫ x, compactZeroExtension K f x * g x) =
      ∫ x in B.carrier, compactZeroExtension K f x * g x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxK : x ∉ K := fun h => hx (hKB h)
    simp [compactZeroExtension, hxK]
  rw [hglobal]
  apply integral_congr_ae
  filter_upwards [compactZeroExtension_ae f hf] with x hx
  rw [hx]

theorem compactZeroExtension_weak_identity {n : ℕ} (B : LocalBall n)
    (w : IntegerSobolev B 1) (K : Set (Space n)) (hK : IsCompact K)
    (hKB : K ⊆ B.carrier)
    (hw : ∀ᵐ x ∂volume.restrict B.carrier, x ∉ K → value w x = 0)
    (α : MultiIndex n 1) (φ : Space n → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (∫ x, compactZeroExtension K (value w) x * coordinateDerivative α φ x) =
      (-1 : ℂ) ^ α.degree *
        (∫ x, compactZeroExtension K (w.derivatives α) x * φ x) := by
  obtain ⟨r, hr, hKr⟩ := exists_pos_lt_subset_ball B.radius_pos hK.isClosed hKB
  let χ : ContDiffBump B.center :=
    ⟨r, (r + B.radius) / 2, hr.1, by linarith [hr.2]⟩
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => (χ x : ℂ) * φ x) :=
    (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul hφ
  have hsupp : tsupport (fun x => (χ x : ℂ) * φ x) ⊆ tsupport χ := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    apply subset_closure
    simp only [Function.mem_support] at hx ⊢
    exact fun hz => hx (by simp [hz])
  have hχB : tsupport χ ⊆ B.carrier := by
    rw [χ.tsupport_eq]
    apply Metric.closedBall_subset_ball
    change (r + B.radius) / 2 < B.radius
    linarith [hr.2]
  let ψ : TestFunction B.toOpens ℂ ⊤ :=
    ⟨fun x => (χ x : ℂ) * φ x, hsmooth,
      χ.hasCompactSupport.isCompact.of_isClosed_subset isClosed_closure hsupp,
      hsupp.trans hχB⟩
  have hψ : ∀ x ∈ K, (fun y => ψ y) =ᶠ[𝓝 x] φ := by
    intro x hx
    filter_upwards [Metric.isOpen_ball.mem_nhds (hKr hx)] with y hy
    change (χ y : ℂ) * φ y = φ y
    rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
    simp
  rw [integral_compactZeroExtension_mul hK hKB (value w) hw,
    integral_compactZeroExtension_mul hK hKB (w.derivatives α)
      (weak_derivatives_zero_off_compact B w K hK hw α)]
  have heq := w.weak_derivatives α ψ
  change (∫ x in B.carrier, value w x * coordinateDerivative α (fun y => ψ y) x) =
    (-1 : ℂ) ^ α.degree * (∫ x in B.carrier, w.derivatives α x * ψ x) at heq
  have hleft : (∫ x in B.carrier, value w x * coordinateDerivative α φ x) =
      ∫ x in B.carrier, value w x * coordinateDerivative α (fun y => ψ y) x := by
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    by_cases hxK : x ∈ K
    · simp only [coordinateDerivative]; rw [(coordinateDerivativeList_congr_nhds α.directions (hψ x hxK)).eq_of_nhds]
    · rw [hx hxK, zero_mul, zero_mul]
  have hright : (∫ x in B.carrier, w.derivatives α x * φ x) =
      ∫ x in B.carrier, w.derivatives α x * ψ x := by
    apply integral_congr_ae
    filter_upwards [weak_derivatives_zero_off_compact B w K hK hw α] with x hx
    by_cases hxK : x ∈ K
    · rw [(hψ x hxK).eq_of_nhds]
    · rw [hx hxK, zero_mul, zero_mul]
  rw [hleft, hright]
  exact heq
theorem directions_length_h1 {n : ℕ} (α : MultiIndex n 1) : α.directions.length = α.degree := by
  simp only [MultiIndex.directions, MultiIndex.degree, List.length_flatMap, List.map_map,
    List.length_replicate, ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

theorem coordinateDerivativeList_reflected_bump {n : ℕ} (φ : ContDiffBump (0 : Space n)) (x y : Space n) (i : Fin n) :
    coordinateDerivativeList [i] (fun z => (φ.normed volume (x - z) : ℂ)) y =
      -(fderiv ℝ (φ.normed volume) (x-y) (EuclideanSpace.single i 1) : ℂ) := by
  simp only [coordinateDerivativeList]
  have hd := (φ.contDiff_normed (μ := volume) (n := (⊤ : ℕ∞))).differentiable (by simp)
  have h := Complex.ofRealCLM.hasFDerivAt.comp y
    ((hd (x-y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x))
  have he : fderiv ℝ (fun z => (φ.normed volume (x - z) : ℂ)) y =
      Complex.ofRealCLM.comp ((fderiv ℝ (φ.normed volume) (x-y)).comp
        (-ContinuousLinearMap.id ℝ (Space n))) := h.fderiv
  rw [he]
  simp
theorem coordinateDerivative_mollification {n : ℕ} (B : LocalBall n)
    (w : IntegerSobolev B 1) (K : Set (Space n)) (hK : IsCompact K)
    (hKB : K ⊆ B.carrier)
    (hw : ∀ᵐ x ∂volume.restrict B.carrier, x ∉ K → value w x = 0)
    (α : MultiIndex n 1) (φ : ContDiffBump (0 : Space n)) (x : Space n) :
    coordinateDerivative α
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        compactZeroExtension K (value w)) x =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        compactZeroExtension K (w.derivatives α)) x := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun z => (φ.normed volume (x - z) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((φ.contDiff_normed).comp (contDiff_const.sub contDiff_id))
  have heq := compactZeroExtension_weak_identity B w K hK hKB hw α _ hs
  have hlen : α.directions.length ≤ 1 := by
    rw [directions_length_h1]; exact α.property
  obtain hnil | ⟨i, hi⟩ : α.directions = [] ∨ ∃ i, α.directions = [i] := by
    cases hl : α.directions with
    | nil => exact Or.inl rfl
    | cons i l =>
      right
      have : l = [] := by cases l <;> simp_all
      exact ⟨i, by simp [this]⟩
  · have hdeg : α.degree = 0 := by simpa [hnil] using (directions_length_h1 α).symm
    simp only [coordinateDerivative, hnil, coordinateDerivativeList, hdeg, pow_zero, one_mul] at heq ⊢
    rw [convolution_eq_swap, convolution_eq_swap]
    simpa only [ContinuousLinearMap.lsmul_apply, Complex.real_smul, mul_comm] using heq
  · have hdeg : α.degree = 1 := by simpa [hi] using (directions_length_h1 α).symm
    simp only [coordinateDerivative, hi, hdeg, pow_one] at heq ⊢
    simp_rw [coordinateDerivativeList_reflected_bump, mul_neg] at heq
    rw [integral_neg] at heq
    have hid := coordinateDerivativeList_singleton_mollification φ
      (compactZeroExtension K (value w))
      ((compactZeroExtension_memLp hK hKB (value w)).locallyIntegrable (by norm_num)) i x
    rw [hid, convolution_eq_swap, convolution_eq_swap]
    simp only [neg_one_mul] at heq
    have heq' := neg_injective heq
    simpa only [ContinuousLinearMap.lsmul_apply, Complex.real_smul, mul_comm] using heq'
theorem averaged_translateL2_integrable {n : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Space n))) (φ : ContDiffBump (0 : Space n)) :
    Integrable (fun t => φ.normed volume t • translateL2 f t) volume := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous.smul (translateL2_continuous f)
  · exact φ.hasCompactSupport_normed.smul_right

 theorem averaged_translateL2_ae {n : ℕ} (g : Space n → ℂ) (hg : MemLp g 2 volume)
    (hg1 : Integrable g volume) (φ : ContDiffBump (0 : Space n)) :
    (∫ t, φ.normed volume t • translateL2 (hg.toLp g) t) =ᵐ[volume]
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
  let f := hg.toLp g
  let a : Lp ℂ 2 (volume : Measure (Space n)) := ∫ t, φ.normed volume t • translateL2 f t
  let c := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  have hc : Continuous c := φ.hasCompactSupport_normed.continuous_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous hg1.locallyIntegrable
  apply ae_eq_of_integral_contDiff_smul_eq (Lp.memLp a |>.locallyIntegrable (by norm_num)) hc.locallyIntegrable
  intro q hq hqc
  have hqLp : MemLp (fun x => (q x : ℂ)) 2 (volume : Measure (Space n)) :=
    (Complex.continuous_ofReal.comp hq.continuous).memLp_of_hasCompactSupport
      (hqc.comp_left rfl)
  let Q := hqLp.toLp (fun x => (q x : ℂ))
  let L := (ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume : Measure (Space n)) 2 2
  have hpair (v : Lp ℂ 2 (volume : Measure (Space n))) :
      L v Q = ∫ x, q x • v x := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hqLp.coeFn_toLp] with x hx
    simp [Q, hx, Complex.real_smul, mul_comm]
  have hbase := (φ.integrable_normed (μ := (volume : Measure (Space n)))).convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hg1
  obtain ⟨C, hC⟩ := (hqc.isCompact_range hq.continuous).isBounded.exists_norm_le
  have hC' (x : Space n) : ‖q x‖ ≤ C := hC _ (Set.mem_range_self x)
  have htriple : Integrable (fun p : Space n × Space n =>
      q p.1 • (φ.normed volume p.2 • g (p.1 - p.2))) (volume.prod volume) := by
    exact hbase.bdd_smul C (hq.continuous.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall (fun p => hC' p.1))
  have ht (t : Space n) : L (translateL2 f t) Q = ∫ x, q x • g (x - t) := by
    rw [hpair]
    apply integral_congr_ae
    have he := Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume t)
    have hf := (measurePreserving_sub_right volume t).quasiMeasurePreserving.ae (hg.coeFn_toLp)
    filter_upwards [he, hf] with x hx hxg
    simp only [Function.comp_apply] at hx
    change q x • ((Lp.compMeasurePreserving (fun x => x - t) _ f) x) = _
    rw [hx]
    change q x • ((hg.toLp g) (x - t)) = _
    rw [hxg]
  rw [← hpair a]
  change L a Q = _
  rw [show L a Q = (L.flip Q) a from rfl]
  dsimp only [a]
  rw [← ContinuousLinearMap.integral_comp_comm _ (averaged_translateL2_integrable f φ)]
  simp only [ContinuousLinearMap.flip_apply]
  have hs (t : Space n) : L (φ.normed volume t • translateL2 f t) Q =
      φ.normed volume t • L (translateL2 f t) Q :=
    (L.flip Q).restrictScalars ℝ |>.map_smul _ _
  simp_rw [hs, ht, ← integral_smul]
  have hswap : Integrable (Function.uncurry fun t x =>
      φ.normed volume t • q x • g (x - t)) (volume.prod volume) := by
    convert htriple.swap using 1
    ext p
    exact smul_comm _ _ _
  rw [integral_integral_swap hswap]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [c, convolution_def, ContinuousLinearMap.lsmul_apply]
    rw [← integral_smul]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => smul_comm _ _ _

private theorem zero_dirs (n k : ℕ) : (zeroIndex n k).directions = [] := by
  simp [MultiIndex.directions, zeroIndex]
private theorem first_dirs {n : ℕ} (i : Fin n) : (firstIndex i).directions = [i] := by
  classical
  simp only [MultiIndex.directions, firstIndex, apply_ite Fin.val, Fin.val_one,
    Fin.val_zero, List.replicate_one, List.replicate_zero]
  have h : ∀ l : List (Fin n), l.flatMap (fun j => if j = i then [j] else []) = l.filter (· = i) := by
    intro l; induction l with
    | nil => rfl
    | cons j l ih => by_cases hj : j = i <;> simp [hj, ih]
  have hrep : ∀ j : Fin n, List.replicate (if j = i then 1 else 0) j =
      if j = i then [j] else [] := by intro j; split_ifs <;> simp
  simp_rw [hrep]
  rw [h, List.filter_eq]
  simp
private theorem cases_idx {n : ℕ} (α : MultiIndex n 1) :
    α = zeroIndex n 1 ∨ ∃ i : Fin n, α = firstIndex i := by
  classical
  by_cases hz : ∀ i, (α.val i).val = 0
  · left; apply Subtype.ext; funext i; apply Fin.ext; exact hz i
  · obtain ⟨i, hi⟩ := not_forall.mp hz
    right; refine ⟨i, ?_⟩
    have hs := Finset.sum_le_one_iff.mp α.property
    have hone := (hs i i (Finset.mem_univ _) (Finset.mem_univ _) hi hi).2
    apply Subtype.ext; funext j; apply Fin.ext
    by_cases hji : j = i
    · subst j; simpa [firstIndex] using hone
    · have hj : (α.val j).val = 0 := by
        by_contra hj
        exact hji (hs j i (Finset.mem_univ _) (Finset.mem_univ _) hj hi).1
      simpa [firstIndex, hji] using hj
private theorem first_degree {n : ℕ} (i : Fin n) : (firstIndex i).degree = 1 := by
  simp only [firstIndex, MultiIndex.degree, apply_ite Fin.val, Fin.val_one, Fin.val_zero]
  simp

private theorem compactZeroExtension_integrable {n : ℕ} {B : LocalBall n}
    {K : Set (Space n)} (hK : IsCompact K) (hKB : K ⊆ B.carrier) (f : BallL2 B) :
    Integrable (compactZeroExtension K f) volume := by
  apply (integrableOn_iff_integrable_of_support_subset
    (Set.support_indicator_subset : Function.support (compactZeroExtension K f) ⊆ K)).mp
  exact ((compactZeroExtension_memLp hK hKB f).locallyIntegrable (by norm_num)).integrableOn_isCompact hK

private theorem mollification_L2 {n : ℕ} (B : LocalBall n)
    (f : BallL2 B) (K : Set (Space n)) (hK : IsCompact K) (hKB : K ⊆ B.carrier)
    (hf : ∀ᵐ x ∂volume.restrict B.carrier, x ∉ K → f x = 0)
    (φ : ℕ → ContDiffBump (0 : Space n))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x in B.carrier,
      ‖((φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        compactZeroExtension K f) x - f x‖ ^ 2) atTop (𝓝 0) := by
  let g := compactZeroExtension K f
  have hg := compactZeroExtension_memLp hK hKB f
  let a := fun m => ∫ t, (φ m).normed volume t • translateL2 (hg.toLp g) t
  let c := fun m => (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  have hae : ∀ m, a m =ᵐ[volume] c m := fun m =>
    averaged_translateL2_ae g hg (compactZeroExtension_integrable hK hKB f) (φ m)
  have hc : ∀ m, MemLp (c m) 2 (volume.restrict B.carrier) := fun m =>
    (MemLp.ae_eq (hae m) (Lp.memLp (a m))).restrict _
  let R := LpToLpRestrictCLM (Space n) ℂ ℝ volume 2 B.carrier
  have heq : ∀ m, (hc m).toLp (c m) = R (a m) := by
    intro m
    apply Lp.ext
    filter_upwards [(hc m).coeFn_toLp,
      LpToLpRestrictCLM_coeFn ℝ B.carrier (a m), ae_restrict_of_ae (hae m)] with x hx hy hz
    exact hx.trans (hz.symm.trans hy.symm)
  have hRf : R (hg.toLp g) = f := by
    apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ B.carrier (hg.toLp g),
      ae_restrict_of_ae hg.coeFn_toLp, compactZeroExtension_ae f hf] with x hx hy hz
    exact hx.trans (hy.trans hz)
  apply integral_norm_sq_sub_tendsto B c hc f
  simp_rw [heq]
  rw [← hRf]
  exact R.continuous.tendsto _ |>.comp (averaged_translateL2_tendsto (hg.toLp g) φ hφ)

private theorem reflected_bump_derivative {n : ℕ}
    (φ : ContDiffBump (0 : Space n)) (i : Fin n) (x y : Space n) :
    coordinateDerivativeList [i] (fun t => (φ.normed volume (x - t) : ℂ)) y =
      -(fderiv ℝ (φ.normed volume) (x - y) (EuclideanSpace.single i 1) : ℂ) := by
  have hd : Differentiable ℝ (φ.normed volume) :=
    (φ.contDiff_normed (n := (⊤ : ℕ∞))).differentiable (by simp)
  simp only [coordinateDerivativeList]
  rw [show (fun t => (φ.normed volume (x - t) : ℂ)) =
    Complex.ofRealCLM ∘ (φ.normed volume) ∘ (fun t => x - t) from rfl]
  rw [fderiv_comp y Complex.ofRealCLM.differentiableAt
    ((hd (x - y)).comp y (differentiableAt_const x |>.sub differentiableAt_id)),
    fderiv_comp y (hd (x - y)) (differentiableAt_const x |>.sub differentiableAt_id)]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
  change (fderiv ℝ (φ.normed volume) (x - y) (fderiv ℝ (fun t => x - t) y
    (EuclideanSpace.single i 1)) : ℂ) = _
  rw [fderiv_const_sub]
  simp

private theorem mollification_weak_derivative {n : ℕ} (B : LocalBall n)
    (w : IntegerSobolev B 1) (K : Set (Space n)) (hK : IsCompact K)
    (hKB : K ⊆ B.carrier)
    (hw : ∀ᵐ x ∂volume.restrict B.carrier, x ∉ K → value w x = 0)
    (φ : ContDiffBump (0 : Space n)) (α : MultiIndex n 1) :
    coordinateDerivative α
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        compactZeroExtension K (value w)) =
      φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        compactZeroExtension K (w.derivatives α) := by
  rcases cases_idx α with rfl | ⟨i, rfl⟩
  · simp only [coordinateDerivative, zero_dirs, coordinateDerivativeList, value]
  · funext x
    rw [coordinateDerivative, first_dirs,
      coordinateDerivativeList_singleton_mollification φ _
        ((compactZeroExtension_memLp hK hKB (value w)).locallyIntegrable (by norm_num))]
    rw [convolution_eq_swap, convolution_eq_swap]
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun t => (φ.normed volume (x - t) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((φ.contDiff_normed).comp (contDiff_const.sub contDiff_id))
    have he := compactZeroExtension_weak_identity B w K hK hKB hw (firstIndex i) _ hs
    simp only [coordinateDerivative, first_dirs, first_degree, pow_one] at he
    simp_rw [reflected_bump_derivative, mul_neg, integral_neg] at he
    simp only [neg_one_mul] at he
    have he' := neg_injective he
    simpa only [ContinuousLinearMap.lsmul_apply, Complex.real_smul, neg_one_mul, mul_comm] using he'

end CompactApproximation

open scoped Convolution

theorem approximate_compact_integerSobolev {n : ℕ} (B : LocalBall n)
    (w : IntegerSobolev B 1) (K : Set (Space n)) (hK : IsCompact K)
    (hKB : K ⊆ B.carrier)
    (hw : ∀ᵐ x ∂volume.restrict B.carrier, x ∉ K → value w x = 0) :
    ∃ φ : ℕ → TestFunction B.toOpens ℂ ⊤,
      ∀ α : MultiIndex n 1,
        Tendsto (fun m => ∫ x in B.carrier,
          ‖coordinateDerivative α (fun y => φ m y) x - w.derivatives α x‖ ^ 2)
          atTop (𝓝 0) := by
  open CompactApproximation in
  obtain ⟨δ, hδ, hδB⟩ := hK.exists_cthickening_subset_open Metric.isOpen_ball hKB
  let ψ : ℕ → TestFunction B.toOpens ℂ ⊤ := fun m =>
    CompactApproximation.mollifiedTest hK hKB (value w)
      (CompactApproximation.shrinkingBump δ hδ m)
      (CompactApproximation.shrinkingBump_rOut_le δ hδ m) hδB
  refine ⟨ψ, fun α => ?_⟩
  have he : ∀ m, coordinateDerivative α (fun y => ψ m y) =
      (CompactApproximation.shrinkingBump δ hδ m).normed volume
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          CompactApproximation.compactZeroExtension K (w.derivatives α) := fun m =>
    CompactApproximation.mollification_weak_derivative B w K hK hKB hw _ α
  simp_rw [he]
  exact CompactApproximation.mollification_L2 B (w.derivatives α) K hK hKB
    (CompactApproximation.weak_derivatives_zero_off_compact B w K hK hw α)
    (CompactApproximation.shrinkingBump δ hδ)
    (CompactApproximation.shrinkingBump_rOut_tendsto δ hδ)

end DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates

end
