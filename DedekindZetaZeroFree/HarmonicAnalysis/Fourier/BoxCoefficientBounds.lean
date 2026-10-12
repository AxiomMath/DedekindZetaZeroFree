module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped Classical ContDiff
open MeasureTheory

namespace DedekindZetaZeroFree.LargeSieve.Vendor.BoxFourier

def phase (t x : ℝ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (x : ℂ))

def coefficient (H : ℝ × ℝ → ℂ) (t s : ℝ) : ℂ :=
  ∫ x : ℝ, ∫ y : ℝ, H (x, y) * phase (-t) x * phase (-s) y

def mixedDeriv (i j : ℕ) (H : ℝ × ℝ → ℂ) (x y : ℝ) : ℂ :=
  iteratedDeriv i (fun u : ℝ => iteratedDeriv j (fun v : ℝ => H (u, v)) y) x

def boxJet (R : ℝ) (H : ℝ × ℝ → ℂ) : ℝ :=
  ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
    sSup {v : ℝ | ∃ x ∈ Set.Icc (-R) R, ∃ y ∈ Set.Icc (-R) R,
      v = ‖mixedDeriv i j H x y‖}

open scoped FourierTransform SchwartzMap
open LineDeriv
set_option maxHeartbeats 800000

abbrev P := WithLp 2 (ℝ × ℝ)
def e : P ≃L[ℝ] ℝ × ℝ := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ
def ax : P := e.symm (1,0)
def ay : P := e.symm (0,1)
def dx (f : 𝓢(P,ℂ)) := ∂_{ax} f
def dy (f : 𝓢(P,ℂ)) := ∂_{ay} f
private lemma dx_eval (f : 𝓢(P,ℂ)) (x y : ℝ) : dx f (e.symm (x,y)) = deriv (fun u => f (e.symm (u,y))) x := by
  rw [dx, SchwartzMap.lineDerivOp_apply]
  unfold lineDeriv
  have hh : (fun t : ℝ => f (e.symm (x,y) + t • ax)) = (fun t => f (e.symm (t+x,y))) := by
    ext t
    congr 1
    apply e.injective
    simp [ax, e, map_add, map_smul]
    ring
  rw [hh]
  simpa only [zero_add] using deriv_comp_add_const (fun u => f (e.symm (u,y))) x 0
private lemma dy_eval (f : 𝓢(P,ℂ)) (x y : ℝ) : dy f (e.symm (x,y)) = deriv (fun u => f (e.symm (x,u))) y := by
  rw [dy, SchwartzMap.lineDerivOp_apply]
  unfold lineDeriv
  have hh : (fun t : ℝ => f (e.symm (x,y) + t • ay)) = (fun t => f (e.symm (x,t+y))) := by
    ext t
    congr 1
    apply e.injective
    simp [ay, e, map_add, map_smul]
    ring
  rw [hh]
  simpa only [zero_add] using deriv_comp_add_const (fun u => f (e.symm (x,u))) y 0
def md (i j : ℕ) (f : 𝓢(P,ℂ)) : 𝓢(P,ℂ) := dx^[i] (dy^[j] f)
private lemma dxn_eval (i : ℕ) (f : 𝓢(P,ℂ)) (x y : ℝ) : (dx^[i] f) (e.symm (x,y)) = iteratedDeriv i (fun u => f (e.symm (u,y))) x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', dx_eval, iteratedDeriv_succ]
    congr 1
    ext u
    exact ih u
private lemma dyn_eval (j : ℕ) (f : 𝓢(P,ℂ)) (x y : ℝ) : (dy^[j] f) (e.symm (x,y)) = iteratedDeriv j (fun u => f (e.symm (x,u))) y := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', dy_eval, iteratedDeriv_succ]
    congr 1
    ext u
    exact ih u
private lemma md_eval (i j : ℕ) (f : 𝓢(P,ℂ)) (x y : ℝ) : md i j f (e.symm (x,y)) = mixedDeriv i j (fun p => f (e.symm p)) x y := by
  rw [md, dxn_eval]
  unfold mixedDeriv
  congr 2
  ext u
  exact dyn_eval j f u y
private lemma fourier_dx (f : 𝓢(P,ℂ)) (t s : ℝ) : 𝓕 (dx f) (e.symm (t,s)) = (2 * Real.pi * Complex.I * (t : ℂ)) * 𝓕 f (e.symm (t,s)) := by
  rw [dx, SchwartzMap.fourier_lineDerivOp_eq]
  have hh : (inner ℝ · ax).HasTemperateGrowth := by fun_prop
  change (2 * Real.pi * Complex.I) • (SchwartzMap.smulLeftCLM ℂ (inner ℝ · ax) (𝓕 f) (e.symm (t,s))) = _
  rw [SchwartzMap.smulLeftCLM_apply_apply hh]
  simp [ax, e, WithLp.prod_inner_apply, Real.inner_apply, smul_eq_mul]
  ring
private lemma fourier_dy (f : 𝓢(P,ℂ)) (t s : ℝ) : 𝓕 (dy f) (e.symm (t,s)) = (2 * Real.pi * Complex.I * (s : ℂ)) * 𝓕 f (e.symm (t,s)) := by
  rw [dy, SchwartzMap.fourier_lineDerivOp_eq]
  have hh : (inner ℝ · ay).HasTemperateGrowth := by fun_prop
  change (2 * Real.pi * Complex.I) • (SchwartzMap.smulLeftCLM ℂ (inner ℝ · ay) (𝓕 f) (e.symm (t,s))) = _
  rw [SchwartzMap.smulLeftCLM_apply_apply hh]
  simp [ay, e, WithLp.prod_inner_apply, Real.inner_apply, smul_eq_mul]
  ring
private lemma fourier_dxn (i : ℕ) (f : 𝓢(P,ℂ)) (t s : ℝ) : 𝓕 (dx^[i] f) (e.symm (t,s)) = (2 * Real.pi * Complex.I * (t : ℂ))^i * 𝓕 f (e.symm (t,s)) := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', fourier_dx, ih]; ring
private lemma fourier_dyn (j : ℕ) (f : 𝓢(P,ℂ)) (t s : ℝ) : 𝓕 (dy^[j] f) (e.symm (t,s)) = (2 * Real.pi * Complex.I * (s : ℂ))^j * 𝓕 f (e.symm (t,s)) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', fourier_dy, ih]; ring
private lemma fourier_md (i j : ℕ) (f : 𝓢(P,ℂ)) (t s : ℝ) : 𝓕 (md i j f) (e.symm (t,s)) = (2 * Real.pi * Complex.I * (t : ℂ))^i * (2 * Real.pi * Complex.I * (s : ℂ))^j * 𝓕 f (e.symm (t,s)) := by
  rw [md, fourier_dxn, fourier_dyn]
  ring
private lemma md_support (i j : ℕ) (f : 𝓢(P,ℂ)) : tsupport (md i j f) ⊆ tsupport f := by
  have hx (i : ℕ) (g : 𝓢(P,ℂ)) : tsupport (dx^[i] g) ⊆ tsupport g := by
    induction i with
    | zero => exact Set.Subset.rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', dx]
      exact (SchwartzMap.tsupport_lineDerivOp_subset ax _).trans ih
  have hy (j : ℕ) : tsupport (dy^[j] f) ⊆ tsupport f := by
    induction j with
    | zero => exact Set.Subset.rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', dy]
      exact (SchwartzMap.tsupport_lineDerivOp_subset ay _).trans ih
  exact (hx i _).trans (hy j)
def box (R : ℝ) : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.Icc (-R) R
def supjet (R : ℝ) (i j : ℕ) (f : 𝓢(P,ℂ)) : ℝ := sSup ((fun p : ℝ × ℝ => ‖md i j f (e.symm p)‖) '' box R)
private lemma sj_nonneg (R : ℝ) (hR : 0 < R) (i j : ℕ) (f : 𝓢(P,ℂ)) : 0 ≤ supjet R i j f := by
  have hc : IsCompact ((fun p : ℝ × ℝ => ‖md i j f (e.symm p)‖) '' box R) := by
    apply (isCompact_Icc.prod isCompact_Icc).image
    exact ((md i j f).continuous.comp e.symm.continuous).norm
  have hm : (0,0) ∈ box R := by dsimp [box]; constructor <;> constructor <;> linarith
  exact (norm_nonneg _).trans (le_csSup hc.bddAbove ⟨(0,0), hm, rfl⟩)
private lemma sj_le (R : ℝ) (i j : ℕ) (f : 𝓢(P,ℂ)) (x y : ℝ) (hp : (x,y) ∈ box R) : ‖md i j f (e.symm (x,y))‖ ≤ supjet R i j f := by
  apply le_csSup (s := (fun p : ℝ × ℝ => ‖md i j f (e.symm p)‖) '' box R) _ ⟨(x,y), hp, rfl⟩
  exact ((isCompact_Icc.prod isCompact_Icc).image (((md i j f).continuous.comp e.symm.continuous).norm)).bddAbove
private lemma fourier_sup_bound (R : ℝ) (hR : 0 < R) (f : 𝓢(P,ℂ))
    (hs : tsupport f ⊆ e ⁻¹' box R) (i j : ℕ) (t s : ℝ) :
    ‖𝓕 (md i j f) (e.symm (t,s))‖ ≤ supjet R i j f * (2 * R)^2 := by
  let g := md i j f
  have he : MeasurePreserving (e : P → ℝ × ℝ) volume (volume.prod volume) := WithLp.volume_preserving_ofLp ℝ ℝ
  have hmass : volume (e ⁻¹' box R) = ENNReal.ofReal (2 * R)^2 := by
    rw [he.measure_preimage (show NullMeasurableSet (box R) (volume.prod volume) from (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet)]
    change (volume.prod volume) (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) = _
    rw [Measure.prod_prod, Real.volume_Icc]
    simp only [sub_neg_eq_add, ← two_mul, pow_two]
  have hmassr : volume.real (e ⁻¹' box R) = (2 * R)^2 := by
    rw [measureReal_def, hmass, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
  have hzero : ∀ p ∉ e ⁻¹' box R, ‖g p‖ = 0 := by
    intro p hp
    rw [show g p = 0 from image_eq_zero_of_notMem_tsupport (fun h => hp (hs (md_support i j f h))), norm_zero]
  have hnorm : ∫ p : P, ‖g p‖ = ∫ p in e ⁻¹' box R, ‖g p‖ := by
    rw [← integral_indicator (show MeasurableSet (e ⁻¹' box R) from (measurableSet_Icc.prod measurableSet_Icc).preimage e.continuous.measurable)]
    congr 1
    ext p
    by_cases hp : p ∈ e ⁻¹' box R
    · simp [hp]
    · simp [hp, hzero p hp]
  calc
    ‖𝓕 g (e.symm (t,s))‖ ≤ ∫ p : P, ‖g p‖ := VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ = ∫ p in e ⁻¹' box R, ‖g p‖ := hnorm
    _ ≤ supjet R i j f * (2 * R)^2 := by
      have hb : ‖∫ p in e ⁻¹' box R, ‖g p‖‖ ≤ supjet R i j f * volume.real (e ⁻¹' box R) := by
        apply norm_setIntegral_le_of_norm_le_const (by rw [hmass]; exact ENNReal.pow_lt_top (ENNReal.ofReal_lt_top) )
        intro p hp
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        have hn := sj_le R i j f (e p).1 (e p).2 hp
        simpa only [Prod.eta, e.symm_apply_apply] using hn
      rw [hmassr, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hb
      exact hb
private lemma weighted_sup_bound (R : ℝ) (hR : 0 < R) (f : 𝓢(P,ℂ))
    (hs : tsupport f ⊆ e ⁻¹' box R) (i j : ℕ) (t s : ℝ) :
    |t|^i * |s|^j * ‖𝓕 f (e.symm (t,s))‖ ≤ supjet R i j f * (2 * R)^2 := by
  have ha : 1 ≤ 2 * Real.pi := by have := Real.two_le_pi; linarith
  have hnorm (u : ℝ) : ‖(2 * Real.pi * Complex.I * (u : ℂ))‖ = (2 * Real.pi) * |u| := by
    simp [norm_mul, Complex.norm_real, abs_of_pos Real.pi_pos]
  have hn := fourier_sup_bound R hR f hs i j t s
  rw [fourier_md, norm_mul, norm_mul, norm_pow, norm_pow, hnorm, hnorm] at hn
  calc
    |t|^i * |s|^j * ‖𝓕 f (e.symm (t,s))‖ ≤ ((2 * Real.pi) * |t|)^i * ((2 * Real.pi) * |s|)^j * ‖𝓕 f (e.symm (t,s))‖ := by
      gcongr
      · exact le_mul_of_one_le_left (abs_nonneg t) ha
      · exact le_mul_of_one_le_left (abs_nonneg s) ha
    _ ≤ _ := hn
private lemma supjet_le_sum (R : ℝ) (hR : 0 < R) (f : 𝓢(P,ℂ)) (i j : ℕ) (hi : i < 3) (hj : j < 3) :
    supjet R i j f ≤ ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, supjet R i j f := by
  apply (Finset.single_le_sum (fun j _ => sj_nonneg R hR i j f) (Finset.mem_range.mpr hj)).trans
  apply Finset.single_le_sum _ (Finset.mem_range.mpr hi)
  intro k hk
  exact Finset.sum_nonneg (fun j _ => sj_nonneg R hR k j f)
private lemma weighted_bound (R : ℝ) (hR : 0 < R) (f : 𝓢(P,ℂ))
    (hs : tsupport f ⊆ e ⁻¹' box R) (t s : ℝ) :
    (1+t^2)*(1+s^2)*‖𝓕 f (e.symm (t,s))‖ ≤ 4 * (2 * R)^2 * (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, supjet R i j f) := by
  have hh (i j : ℕ) (hi : i < 3) (hj : j < 3) :=
    (weighted_sup_bound R hR f hs i j t s).trans (mul_le_mul_of_nonneg_right (supjet_le_sum R hR f i j hi hj) (sq_nonneg (2*R)))
  have h00 := hh 0 0 (by decide) (by decide)
  have h20 := hh 2 0 (by decide) (by decide)
  have h02 := hh 0 2 (by decide) (by decide)
  have h22 := hh 2 2 (by decide) (by decide)
  simp only [pow_zero, sq_abs, one_mul, mul_one] at h00 h20 h02 h22
  nlinarith [h00, h20, h02, h22]

def lifted (H : ℝ × ℝ → ℂ) : P → ℂ := fun p => H p.ofLp
def sm (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) : 𝓢(P,ℂ) :=
  (hc.comp_homeomorph e.toHomeomorph).toSchwartzMap (hH.comp e.contDiff)
private lemma np (t x : ℝ) : ‖phase t x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp
private lemma kernel (p q : P) :
    Complex.exp (↑(-2 * Real.pi * inner ℝ p q) * Complex.I) =
      phase (-q.ofLp.1) p.ofLp.1 * phase (-q.ofLp.2) p.ofLp.2 := by
  simp only [phase, ← Complex.exp_add]
  congr 1
  simp only [WithLp.prod_inner_apply, Real.inner_apply]
  push_cast
  ring
private lemma coef (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) (t s : ℝ) :
    coefficient H t s = 𝓕 (lifted H) ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm (t,s)) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ
  have he : MeasurePreserving (e : P → ℝ × ℝ) volume (volume.prod volume) :=
    WithLp.volume_preserving_ofLp ℝ ℝ
  have hi : Integrable (fun p : ℝ × ℝ => H p * phase (-t) p.1 * phase (-s) p.2)
      (volume.prod volume) := by
    refine Integrable.mono' (hH.continuous.integrable_of_hasCompactSupport hc).norm ?_ ?_
    · apply Continuous.aestronglyMeasurable
      dsimp [phase]
      fun_prop
    · filter_upwards with p
      simp only [norm_mul, np, mul_one, le_refl]
  rw [Real.fourier_eq']
  simp_rw [kernel]
  simp only [smul_eq_mul]
  change coefficient H t s = ∫ p : P, (phase (-t) p.ofLp.1 * phase (-s) p.ofLp.2) * H p.ofLp
  rw [show (∫ p : P, (phase (-t) p.ofLp.1 * phase (-s) p.ofLp.2) * H p.ofLp) =
      ∫ p : P, (fun q : ℝ × ℝ => H q * phase (-t) q.1 * phase (-s) q.2) (e p) by
    apply integral_congr_ae
    filter_upwards with p
    change phase (-t) p.ofLp.1 * phase (-s) p.ofLp.2 * H p.ofLp =
      H p.ofLp * phase (-t) p.ofLp.1 * phase (-s) p.ofLp.2
    ring]
  rw [he.integral_comp e.toHomeomorph.measurableEmbedding (fun q => H q * phase (-t) q.1 * phase (-s) q.2), integral_prod _ hi]
  rfl
private lemma finish (R : ℝ) (hR : 0 < R) (H : ℝ × ℝ → ℂ)
    (hH : ContDiff ℝ ∞ H) (hs : Function.support H ⊆ box R) (t s : ℝ) :
    (1+t^2)*(1+s^2)*‖coefficient H t s‖ ≤ 4 * (2 * R)^2 * boxJet R H := by
  have hclosed : IsClosed (box R) := isClosed_Icc.prod isClosed_Icc
  have hts : tsupport H ⊆ box R := closure_minimal hs hclosed
  have hc : HasCompactSupport H := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_closure hts
  let f := sm H hH hc
  have hf : ∀ p : P, f p = H (e p) := fun _ => rfl
  have hsf : tsupport f ⊆ e ⁻¹' box R := by
    apply closure_minimal _ (hclosed.preimage e.continuous)
    intro p hp
    apply hs
    exact hp
  have hjet : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, supjet R i j f) = boxJet R H := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    unfold supjet
    apply congrArg sSup
    ext v
    constructor
    · rintro ⟨⟨x,y⟩, hxy, rfl⟩
      refine ⟨x, hxy.1, y, hxy.2, ?_⟩
      dsimp only
      rw [md_eval]
      have heq : (fun p => f (e.symm p)) = H := by ext p; rw [hf, e.apply_symm_apply]
      rw [heq]
    · rintro ⟨x,hx,y,hy,rfl⟩
      refine ⟨(x,y), ⟨hx,hy⟩, ?_⟩
      dsimp only
      rw [md_eval]
      have heq : (fun p => f (e.symm p)) = H := by ext p; rw [hf, e.apply_symm_apply]
      rw [heq]
  have hh := weighted_bound R hR f hsf t s
  rw [hjet] at hh
  rw [coef H hH hc]
  exact hh

theorem coefficient_box_bound (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ × ℝ → ℂ,
      ContDiff ℝ ∞ H →
      Function.support H ⊆ Set.Icc (-R) R ×ˢ Set.Icc (-R) R →
      ∀ t s : ℝ,
        (1 + t ^ 2) * (1 + s ^ 2) * ‖coefficient H t s‖ ≤ C * boxJet R H := by
  refine ⟨4 * (2 * R)^2, by positivity, ?_⟩
  intro H hH hs t s
  exact finish R hR H hH hs t s

end DedekindZetaZeroFree.LargeSieve.Vendor.BoxFourier

end
