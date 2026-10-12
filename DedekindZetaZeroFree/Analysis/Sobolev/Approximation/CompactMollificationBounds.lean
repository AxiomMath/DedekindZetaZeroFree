module

public import DedekindZetaZeroFree.Analysis.Sobolev.WeakDerivatives.CutoffZeroExtension
public import DedekindZetaZeroFree.Analysis.Sobolev.Approximation.CompactInteriorH1Density

@[expose] public section

noncomputable section

set_option maxHeartbeats 1500000

namespace DedekindZetaZeroFree.KPLocalCubeSobolevJets.Interior

open MeasureTheory KPContLocalNorm
open scoped Convolution

theorem exists_box_for_compact_thickening {n : ℕ} (K : Set (Space n)) (hK : IsCompact K) :
    ∃ lower upper : Fin n → ℝ, (∀ i, lower i < upper i) ∧
      Metric.cthickening 1 K ⊆ {x | ∀ i, lower i < x i ∧ x i < upper i} := by
  have hc : IsCompact (Metric.cthickening 1 K) := hK.cthickening
  have hlow (i : Fin n) : BddBelow ((fun x : Space n => x i) '' Metric.cthickening 1 K) :=
    hc.bddBelow_image (by fun_prop)
  have hupp (i : Fin n) : BddAbove ((fun x : Space n => x i) '' Metric.cthickening 1 K) :=
    hc.bddAbove_image (by fun_prop)
  choose l hl using hlow
  choose u hu using hupp
  refine ⟨fun i => min (l i) (u i) - 1, fun i => max (l i) (u i) + 1, ?_, ?_⟩
  · intro i
    have : min (l i) (u i) ≤ max (l i) (u i) := min_le_max
    dsimp only
    linarith
  · intro x hx i
    have hlx := hl i (Set.mem_image_of_mem (fun x : Space n => x i) hx)
    have hux := hu i (Set.mem_image_of_mem (fun x : Space n => x i) hx)
    have hmin := min_le_left (l i) (u i)
    have hmax := le_max_right (l i) (u i)
    constructor <;> dsimp only <;> linarith

theorem norm_averaged_translateL2_le {n : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Space n))) (φ : ContDiffBump (0 : Space n)) :
    ‖∫ t, φ.normed volume t • KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2 f t‖ ≤ ‖f‖ := by
  calc
    _ ≤ ∫ t, ‖φ.normed volume t • KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2 f t‖ := norm_integral_le_integral_norm _
    _ = ∫ t, φ.normed volume t * ‖f‖ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t), KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2_norm]
    _ = ‖f‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]

theorem convolution_integral_norm_sq_le {n : ℕ}
    (g : Space n → ℂ) (hg : MemLp g 2 volume) (hg1 : Integrable g volume)
    (φ : ContDiffBump (0 : Space n)) :
    (∫ x, ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ^ 2) ≤
      ‖hg.toLp g‖ ^ 2 := by
  let a : Lp ℂ 2 (volume : Measure (Space n)) :=
    ∫ t, φ.normed volume t • KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2 (hg.toLp g) t
  have hae := KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.averaged_translateL2_ae g hg hg1 φ
  have heq : (∫ x, ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ^ 2) = ‖a‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  rw [heq]
  exact pow_le_pow_left₀ (norm_nonneg a) (norm_averaged_translateL2_le _ φ) 2

private theorem smooth_coordinateDerivativeList {n : ℕ} (l : List (Fin n))
    {φ : Space n → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivativeList l φ) := by
  induction l with
  | nil => exact hφ
  | cons i l ih =>
      exact (ih.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

private theorem compactSupport_coordinateDerivativeList {n : ℕ} (l : List (Fin n))
    {f : Space n → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (coordinateDerivativeList l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih =>
      exact ih.of_isClosed_subset isClosed_closure
        ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)) : _)

private theorem coordinateDerivativeList_convolution_smooth_left {n : ℕ}
    (φ : Space n → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (g : Space n → ℂ)
    (hg : LocallyIntegrable g volume) (l : List (Fin n)) (x : Space n) :
    coordinateDerivativeList l
      (φ ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] g) x =
      ((coordinateDerivativeList l φ)
        ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] g) x := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
      have hi (y : Space n) := ih y
      have hD := smooth_coordinateDerivativeList l hφ
      have hC := compactSupport_coordinateDerivativeList l hc
      change (fderiv ℝ (coordinateDerivativeList l (φ ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] g)) x)
        (EuclideanSpace.single i 1) = _
      rw [show (coordinateDerivativeList l (φ ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] g)) =
        ((coordinateDerivativeList l φ) ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] g) from funext hi]
      rw [(hC.hasFDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℂ)
        (hD.of_le (by simp)) hg x).fderiv]
      unfold convolution
      have h_int := (hC.fderiv ℝ).convolutionExists_left
        (ContinuousLinearMap.precompL (Space n) (ContinuousLinearMap.mul ℝ ℂ))
        (hD.fderiv_right (m := (1 : ℕ∞)) (by simp)).continuous hg x
      rw [ContinuousLinearMap.integral_apply h_int]
      simp only [ContinuousLinearMap.precompL_apply, coordinateDerivativeList]
private theorem coordinateDerivativeList_reflection {n : ℕ}
    (φ : Space n → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (l : List (Fin n)) (x y : Space n) :
    coordinateDerivativeList l (fun z => φ (x-z)) y =
      (-1 : ℂ) ^ l.length * coordinateDerivativeList l φ (x-y) := by
  induction l generalizing y with
  | nil => simp [coordinateDerivativeList]
  | cons i l ih =>
      have hd := smooth_coordinateDerivativeList l hφ
      have hcomp := ((hd.differentiable (by simp)).differentiableAt.hasFDerivAt).comp y
        ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
      have heq : coordinateDerivativeList l (fun z => φ (x-z)) =
        fun z => (-1 : ℂ)^l.length * coordinateDerivativeList l φ (x-z) := funext ih
      change fderiv ℝ (coordinateDerivativeList l (fun z => φ (x-z))) y
        (EuclideanSpace.single i 1) = _
      rw [heq]
      have hd' := (hcomp.const_mul ((-1 : ℂ)^l.length)).fderiv
      dsimp only [Function.comp_def, Pi.sub_apply, id_eq] at hd'
      rw [hd']
      simp [coordinateDerivativeList, pow_succ, mul_neg, mul_assoc]

private theorem multiIndex_directions_length {n k : ℕ} (α : MultiIndex n k) :
    α.directions.length = α.degree := by
  simp only [MultiIndex.directions, MultiIndex.degree, List.length_flatMap, List.map_map,
    List.length_replicate, ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

theorem global_weak_coordinateDerivative_convolution {n k : ℕ}
    (g : GlobalWeakSobolev n k) (φ : Space n → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (α : MultiIndex n k) (x : Space n) :
    coordinateDerivative α
      (φ ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
        (fun y => g.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) y)) x =
      (φ ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
        (fun y => g.derivatives α y)) x := by
  let ψ : TestFunction (⊤ : TopologicalSpace.Opens (Space n)) ℂ ⊤ :=
    ⟨fun z => φ (x-z), hφ.comp (contDiff_const.sub contDiff_id),
      (by simpa [Function.comp_def] using (hc.comp_homeomorph
        ((Homeomorph.subRight x).trans (Homeomorph.neg (Space n))))), by simp⟩
  have heq := g.weak_derivatives α ψ
  have hψ : (fun z => ψ z) = (fun z => φ (x-z)) := rfl
  rw [hψ] at heq
  simp only [coordinateDerivative] at heq ⊢
  simp_rw [coordinateDerivativeList_reflection φ hφ] at heq
  rw [multiIndex_directions_length α] at heq
  simp_rw [mul_left_comm _ ((-1 : ℂ)^α.degree)] at heq
  rw [integral_const_mul] at heq
  have hcancel : (-1 : ℂ)^α.degree ≠ 0 := pow_ne_zero _ (by norm_num)
  have heq' := mul_left_cancel₀ hcancel heq
  rw [coordinateDerivativeList_convolution_smooth_left φ hφ hc _
    ((Lp.memLp _).locallyIntegrable (by norm_num))]
  rw [convolution_eq_swap, convolution_eq_swap]
  simpa only [ContinuousLinearMap.mul_apply', ψ, TestFunction.coe_mk, mul_comm] using heq'

def unitBump (n : ℕ) : ContDiffBump (0 : Space n) := ⟨1/2, 1, by norm_num, by norm_num⟩
def radiusBump (n : ℕ) (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : Space n) :=
  ⟨r/2, r, by positivity, by linarith⟩

theorem radiusBump_eq_scaled {n : ℕ} (r : ℝ) (hr : 0 < r) (x : Space n) :
    radiusBump n r hr x = unitBump n (r⁻¹ • x) := by
  rw [ContDiffBump.apply, ContDiffBump.apply]
  change (someContDiffBumpBase (Space n)).toFun (r / (r / 2)) ((r / 2)⁻¹ • (x - 0)) =
    (someContDiffBumpBase (Space n)).toFun (1 / (1 / 2)) ((1 / 2)⁻¹ • (r⁻¹ • x - 0))
  rw [sub_zero, sub_zero, smul_smul]
  have h₁ : r / (r / 2) = (1 : ℝ) / (1 / 2) := by field_simp
  have h₂ : (r / 2)⁻¹ = (1 / 2 : ℝ)⁻¹ * r⁻¹ := by field_simp
  rw [h₁, h₂]

theorem radiusBump_integral {n : ℕ} (r : ℝ) (hr : 0 < r) :
    (∫ x, radiusBump n r hr x) = r^n * (∫ x, unitBump n x) := by
  simp_rw [radiusBump_eq_scaled]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume _ hr.le]
  simp [finrank_euclideanSpace, smul_eq_mul]

theorem mollify_eq_radiusBump_convolution {n : ℕ} (r : ℝ) (hr : 0 < r)
    (h : Space n → ℂ) (x : Space n) :
    (∫ y, ((unitBump n).normed volume y : ℂ) * h (x - r • y)) =
    ((radiusBump n r hr).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) x := by
  have heq := Measure.integral_comp_smul_of_nonneg volume
    (fun z => ((radiusBump n r hr).normed volume z : ℂ) * h (x-z)) r (hR := hr.le)
  have hscale (y : Space n) : (radiusBump n r hr).normed volume (r • y) =
      (r^n)⁻¹ * (unitBump n).normed volume y := by
    rw [ContDiffBump.normed_def, radiusBump_eq_scaled, inv_smul_smul₀ hr.ne', radiusBump_integral,
      ContDiffBump.normed_def]
    field_simp
  simp_rw [hscale, Complex.ofReal_mul, mul_assoc] at heq
  rw [integral_const_mul] at heq
  rw [← Complex.real_smul] at heq
  have hrn : (r^n)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hr.ne')
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin] at heq
  have heq' := (smul_right_injective ℂ hrn) heq
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, Complex.real_smul] using heq'

private theorem complex_convolution_eq_real {n : ℕ} (φ : Space n → ℝ) (h : Space n → ℂ) :
    ((fun y => (φ y : ℂ)) ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] h) =
      (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) := by
  ext x
  simp only [convolution_def, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply, Complex.real_smul]

private theorem weak_derivative_real_convolution {n k : ℕ} (g : GlobalWeakSobolev n k)
    (φ : Space n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (α : MultiIndex n k) :
    coordinateDerivative α
      (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun y => g.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) y)) =
      (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun y => g.derivatives α y)) := by
  ext x
  have heq := global_weak_coordinateDerivative_convolution g (fun y => (φ y : ℂ))
    (Complex.ofRealCLM.contDiff.comp hφ)
    (show HasCompactSupport (fun y => (φ y : ℂ)) from hc.comp_left (g := Complex.ofReal) rfl) α x
  simpa only [complex_convolution_eq_real] using heq

private theorem compact_representative {n : ℕ} (f : Lp ℂ 2 (volume : Measure (Space n)))
    {K : Set (Space n)} (hK : IsCompact K) (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    K.indicator (fun x => f x) =ᵐ[volume] (fun x => f x) := by
  filter_upwards [hf] with x hx
  by_cases h : x ∈ K <;> simp [h, hx]

private theorem compact_lp_integrable {n : ℕ} (f : Lp ℂ 2 (volume : Measure (Space n)))
    {K : Set (Space n)} (hK : IsCompact K) (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    Integrable (fun x => f x) volume := by
  have he := compact_representative f hK hf
  apply Integrable.congr _ he
  apply (integrableOn_iff_integrable_of_support_subset Set.support_indicator_subset).mp
  exact ((Lp.memLp f).locallyIntegrable (by norm_num)).integrableOn_isCompact hK |>.indicator hK.measurableSet

private theorem lp_toLp_norm {n : ℕ} (f : Lp ℂ 2 (volume : Measure (Space n))) :
    ‖(Lp.memLp f).toLp (fun x => f x)‖ = ‖f‖ := by
  congr 1
  exact Lp.toLp_coeFn f (Lp.memLp f)

private theorem compact_ae_convolution_tsupport {n : ℕ}
    (φ : ContDiffBump (0 : Space n))
    (f : Lp ℂ 2 (volume : Measure (Space n)))
    {K : Set (Space n)} (hK : IsCompact K) (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    tsupport (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun x => f x)) ⊆
      Metric.cthickening φ.rOut K := by
  have he := compact_representative f hK hf
  rw [← convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
    (Filter.Eventually.of_forall fun y => (rfl : φ.normed volume y = φ.normed volume y)) he]
  exact KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.convolution_tsupport_subset_thickening φ hK
    (closure_minimal Set.support_indicator_subset hK.isClosed) le_rfl

def mollify {n : ℕ} (φ : Space n → ℝ) (δ : ℝ)
    (h : Space n → ℂ) (t : ℕ) (x : Space n) : ℂ :=
  ∫ y, (φ y : ℂ) * h (x - (δ / (t + 1 : ℕ)) • y)

theorem compact_weak_mollification_on_box {n : ℕ} (hn : 0 < n)
    (k : ℕ) (K : Set (Space n)) (hK : IsCompact K) :
    ∃ (lower upper : Fin n → ℝ), (∀ i, lower i < upper i) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ φ : Space n → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
        tsupport φ ⊆ Metric.closedBall 0 1 ∧
        (∀ y, 0 ≤ φ y) ∧ (∫ y, φ y) = 1 ∧
        ∀ (g : GlobalWeakSobolev n k),
          (∀ α : MultiIndex n k, ∀ᵐ x ∂volume,
            x ∉ K → g.derivatives α x = 0) →
          ∀ t : ℕ,
            let w := mollify φ δ
              (fun x => g.derivatives
                (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x) t
            ContDiff ℝ (⊤ : ℕ∞) w ∧ HasCompactSupport w ∧
              tsupport w ⊆ {x | ∀ i, lower i < x i ∧ x i < upper i} ∧
              Real.sqrt (∑ β : MultiIndex n k,
                ∫ y, ‖coordinateDerivative β w y‖ ^ 2) ≤
                Real.sqrt (∑ β : MultiIndex n k, ‖g.derivatives β‖ ^ 2) := by
  obtain ⟨lower, upper, hbox, hcontain⟩ := exists_box_for_compact_thickening K hK
  let b := unitBump n
  refine ⟨lower, upper, hbox, 1, by norm_num, b.normed volume,
    b.contDiff_normed, b.hasCompactSupport_normed, ?_, b.nonneg_normed, b.integral_normed, ?_⟩
  · rw [b.tsupport_normed_eq]
    exact Set.Subset.rfl
  · intro g hg t
    let r : ℝ := 1 / (t + 1 : ℕ)
    have hr : 0 < r := by dsimp [r]; positivity
    have hr1 : r ≤ 1 := by dsimp [r]; exact div_le_self (by norm_num) (by norm_cast; omega)
    let a := radiusBump n r hr
    let f : Lp ℂ 2 (volume : Measure (Space n)) :=
      g.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k)
    have hw : mollify (b.normed volume) 1 (fun x => f x) t =
      (a.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun x => f x)) := by
      ext x
      exact mollify_eq_radiusBump_convolution r hr _ x
    change ContDiff ℝ (⊤ : ℕ∞) (mollify _ _ _ _) ∧ _
    rw [hw]
    refine ⟨a.hasCompactSupport_normed.contDiff_convolution_left _ a.contDiff_normed
      ((Lp.memLp f).locallyIntegrable (by norm_num)), ?_, ?_, ?_⟩
    · have hs := compact_ae_convolution_tsupport a f hK (hg _)
      exact (hK.cthickening (r := r)).of_isClosed_subset isClosed_closure hs
    · exact (compact_ae_convolution_tsupport a f hK (hg _)).trans
        ((Metric.cthickening_mono hr1 K).trans hcontain)
    · apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro β hβ
      rw [weak_derivative_real_convolution g _ a.contDiff_normed a.hasCompactSupport_normed β]
      have hb := convolution_integral_norm_sq_le (fun x => g.derivatives β x)
        (Lp.memLp _) (compact_lp_integrable _ hK (hg β)) a
      simpa only [lp_toLp_norm] using hb

end DedekindZetaZeroFree.KPLocalCubeSobolevJets.Interior

end
