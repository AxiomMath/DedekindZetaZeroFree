module

public import DedekindZetaZeroFree.Moments.Reflected.SeparatedProfileExpansion

@[expose] public section

namespace DedekindZetaZeroFree.RMFourierProfile
noncomputable section
open MeasureTheory
open scoped ContDiff

def IsCutoff (ξ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ ξ ∧ HasCompactSupport ξ ∧
    Set.EqOn ξ (fun _ => 1) (Set.Icc (-2 * Real.log 2) (Real.log 2))

def UniformLogBounds {I : Type*} (P : I → ℝ → ℂ) : Prop :=
  (∀ i, ContDiff ℝ 2 (logProfile (P i))) ∧
    ∀ B : ℝ, 0 < B → ∃ K : ℝ, 0 < K ∧
      ∀ (i : I) (k : ℕ), k ≤ 2 → ∀ y : ℝ, 0 < y →
        ‖iteratedDeriv k (logProfile (P i)) (Real.log y)‖ ≤
          K * min (Real.rpow y (1 / 8)) (Real.rpow y (-B))

def localizedProfile (ξ : ℝ → ℝ) (Φ : ℝ → ℂ) (v : ℝ) : ℝ → ℂ :=
  fun x => (ξ x : ℂ) * Φ (v * Real.exp x)

def normPhase (t r : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * t * Real.log r : ℝ) * Complex.I)

theorem norm_normPhase (t r : ℝ) (hr : 0 < r) :
    ‖normPhase t r‖ = 1 := by
  simp [normPhase, Complex.norm_exp]

private theorem fourier_norm_le (g : ℝ → ℂ) (t : ℝ) :
    ‖FourierTransform.fourier g t‖ ≤ ∫ x : ℝ, ‖g x‖ := by
  rw [Real.fourier_eq]
  calc
    ‖∫ x : ℝ, Real.fourierChar (-inner ℝ x t) • g x‖ ≤
        ∫ x : ℝ, ‖Real.fourierChar (-inner ℝ x t) • g x‖ := norm_integral_le_integral_norm _
    _ = _ := by simp

private theorem fourier_c2_majorant (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g)
    (hgi : ∀ n : ℕ, n ≤ 2 → Integrable (iteratedDeriv n g)) (t : ℝ) :
    ‖FourierTransform.fourier g t‖ ≤
      ((∫ x : ℝ, ‖g x‖) + (∫ x : ℝ, ‖iteratedDeriv 2 g x‖)) * (1 + t ^ 2)⁻¹ := by
  have hft := Real.fourier_iteratedDeriv (N := 2) (n := 2) hg
    (fun n hn => hgi n (by exact_mod_cast hn)) (by norm_num)
  have hpoint := congrFun hft t
  have hdecay := fourier_norm_le (iteratedDeriv 2 g) t
  rw [hpoint, norm_smul, norm_pow] at hdecay
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hdecay
  norm_num at hdecay
  have hsmall := fourier_norm_le g t
  have hcoef : 1 ≤ (2 * Real.pi) ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hsq : (2 * Real.pi * |t|) ^ 2 = (2 * Real.pi) ^ 2 * t ^ 2 := by
    rw [mul_pow, sq_abs]
  rw [hsq] at hdecay
  have hlarge : t ^ 2 * ‖FourierTransform.fourier g t‖ ≤
      ∫ x : ℝ, ‖iteratedDeriv 2 g x‖ := by
    calc
      t ^ 2 * ‖FourierTransform.fourier g t‖ ≤
          (2 * Real.pi) ^ 2 * (t ^ 2 * ‖FourierTransform.fourier g t‖) :=
        le_mul_of_one_le_left (by positivity) hcoef
      _ ≤ _ := by simpa only [mul_assoc] using hdecay
  have hsum : (1 + t ^ 2) * ‖FourierTransform.fourier g t‖ ≤
      (∫ x : ℝ, ‖g x‖) + (∫ x : ℝ, ‖iteratedDeriv 2 g x‖) := by nlinarith
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).2
  nlinarith

theorem fourier_c2_l1_bound (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g)
    (hgi : ∀ n : ℕ, n ≤ 2 → Integrable (iteratedDeriv n g)) :
    Integrable (FourierTransform.fourier g) ∧
    (∫ t : ℝ, ‖FourierTransform.fourier g t‖) ≤
      ((∫ x : ℝ, ‖g x‖) + (∫ x : ℝ, ‖iteratedDeriv 2 g x‖)) *
        (∫ t : ℝ, (1 + t ^ 2)⁻¹) := by
  let M := (∫ x : ℝ, ‖g x‖) + (∫ x : ℝ, ‖iteratedDeriv 2 g x‖)
  have hint : Integrable (fun t : ℝ => M * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul M
  have hf : Integrable (FourierTransform.fourier g) :=
    hint.mono' (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_fst.inner continuous_snd)
      (by simpa using hgi 0 (by omega))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fourier_c2_majorant g hg hgi))
  refine ⟨hf, ?_⟩
  calc
    (∫ t : ℝ, ‖FourierTransform.fourier g t‖) ≤ ∫ t : ℝ, M * (1 + t ^ 2)⁻¹ :=
      integral_mono hf.norm hint (fourier_c2_majorant g hg hgi)
    _ = _ := integral_const_mul _ _

private theorem compact_iterated {f : ℝ → ℂ} (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n f) := by
  induction n with
  | zero => simpa using hf
  | succ n hn => simpa only [iteratedDeriv_succ] using hn.deriv

private theorem second_product (a f : ℝ → ℂ) (ha : ContDiff ℝ 2 a)
    (hf : ContDiff ℝ 2 f) (x : ℝ) :
    iteratedDeriv 2 (a * f) x =
      iteratedDeriv 2 a x * f x + 2 * deriv a x * deriv f x + a x * iteratedDeriv 2 f x := by
  rw [iteratedDeriv_mul ha.contDiffAt hf.contDiffAt]
  simp [Finset.sum_range_succ, iteratedDeriv_one]
  <;> ring

private theorem scaled_envelope (v x B : ℝ) (hv : 0 < v) :
    min (Real.rpow (v * Real.exp x) (1 / 8)) (Real.rpow (v * Real.exp x) (-B)) ≤
      (Real.exp (x * (1 / 8)) + Real.exp (x * (-B))) *
        min (Real.rpow v (1 / 8)) (Real.rpow v (-B)) := by
  have hp (r : ℝ) : Real.rpow (v * Real.exp x) r =
      Real.rpow v r * Real.exp (x * r) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow hv.le (Real.exp_pos x).le,
      Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
  rw [hp, hp, mul_min_of_nonneg _ _ (by positivity)]
  simp only [Real.rpow_eq_pow]
  apply min_le_min
  · nlinarith [Real.rpow_pos_of_pos hv (1 / 8), Real.exp_pos (x * (-B))]
  · nlinarith [Real.rpow_pos_of_pos hv (-B), Real.exp_pos (x * (1 / 8))]

set_option maxHeartbeats 1200000 in

theorem uniform_fourier_l1 {I : Type*} [Fintype I]
    (ξ : ℝ → ℝ) (hξ : IsCutoff ξ) (P : I → ℝ → ℂ)
    (hP : UniformLogBounds P) :
    ∀ B : ℝ, 0 < B → ∃ K : ℝ, 0 < K ∧
      ∀ (i : I) (v : ℝ), 0 < v →
        Integrable (localizedProfile ξ (P i) v) ∧
        Integrable (FourierTransform.fourier (localizedProfile ξ (P i) v)) ∧
        (∫ t : ℝ, ‖FourierTransform.fourier (localizedProfile ξ (P i) v) t‖) ≤
          K * min (Real.rpow v (1 / 8)) (Real.rpow v (-B)) := by
  intro B hB
  obtain ⟨L, hL, henv⟩ := hP.2 B hB
  let a : ℝ → ℂ := fun x => (ξ x : ℂ)
  have ha : ContDiff ℝ 2 a :=
    Complex.ofRealCLM.contDiff.comp (hξ.1.of_le (by norm_num))
  have hac : HasCompactSupport a := hξ.2.1.comp_left (g := Complex.ofReal) (by simp)
  let E : ℝ → ℝ := fun x => Real.exp (x * (1 / 8)) + Real.exp (x * (-B))
  have hEc : Continuous E := by dsimp [E]; fun_prop
  have hE (x : ℝ) : 0 ≤ E x := by dsimp [E]; positivity
  let W0 : ℝ → ℝ := fun x => ‖a x‖ * E x
  let W2 : ℝ → ℝ := fun x =>
    (‖iteratedDeriv 2 a x‖ + 2 * ‖iteratedDeriv 1 a x‖ + ‖a x‖) * E x
  have hW0 : Integrable W0 :=
    (ha.continuous.norm.mul hEc).integrable_of_hasCompactSupport hac.norm.mul_right
  have hW2 : Integrable W2 := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (((ha.continuous_iteratedDeriv 2 (by norm_num)).norm.add
        (continuous_const.mul (ha.continuous_iteratedDeriv 1 (by norm_num)).norm)).add
        ha.continuous.norm).mul hEc
    · exact (((compact_iterated hac 2).norm.add
        ((compact_iterated hac 1).norm.mul_left)).add hac.norm).mul_right
  have hW0pos : 0 ≤ ∫ x, W0 x := integral_nonneg (fun x => mul_nonneg (norm_nonneg _) (hE x))
  have hW2pos : 0 ≤ ∫ x, W2 x := integral_nonneg (by intro x; dsimp [W2]; positivity)
  let J : ℝ := ∫ t : ℝ, (1 + t ^ 2)⁻¹
  have hJ : 0 ≤ J := integral_nonneg (by intro t; positivity)
  refine ⟨L * ((∫ x, W0 x) + (∫ x, W2 x)) * J + 1, by positivity, ?_⟩
  intro i v hv
  let f : ℝ → ℂ := fun x => logProfile (P i) (x + Real.log v)
  have hf : ContDiff ℝ 2 f := (hP.1 i).comp (contDiff_id.add contDiff_const)
  have heq : localizedProfile ξ (P i) v = a * f := by
    funext x
    simp [localizedProfile, a, f, logProfile, Real.exp_add, Real.exp_log hv, mul_comm]
  have hg : ContDiff ℝ 2 (a * f) := ha.mul hf
  have hgc : HasCompactSupport (a * f) := hac.mul_right
  have hgi : ∀ n : ℕ, n ≤ 2 → Integrable (iteratedDeriv n (a * f)) := by
    intro n hn
    exact (hg.continuous_iteratedDeriv n (by exact_mod_cast hn)).integrable_of_hasCompactSupport
      (compact_iterated hgc n)
  let m : ℝ := min (Real.rpow v (1 / 8)) (Real.rpow v (-B))
  have hm : 0 ≤ m := by dsimp [m]; exact le_min (Real.rpow_pos_of_pos hv _).le (Real.rpow_pos_of_pos hv _).le
  have hfb (n : ℕ) (hn : n ≤ 2) (x : ℝ) :
      ‖iteratedDeriv n f x‖ ≤ L * E x * m := by
    rw [show f = (fun x => logProfile (P i) (x + Real.log v)) from rfl,
      iteratedDeriv_comp_add_const]
    have hb := henv i n hn (v * Real.exp x) (mul_pos hv (Real.exp_pos x))
    rw [Real.log_mul hv.ne' (Real.exp_pos x).ne', Real.log_exp, add_comm] at hb
    calc
      _ ≤ L * min (Real.rpow (v * Real.exp x) (1 / 8))
          (Real.rpow (v * Real.exp x) (-B)) := hb
      _ ≤ L * (E x * m) := mul_le_mul_of_nonneg_left (scaled_envelope v x B hv) hL.le
      _ = _ := by ring
  have hb0 (x : ℝ) : ‖(a * f) x‖ ≤ W0 x * (L * m) := by
    have h := hfb 0 (by omega) x
    simp only [iteratedDeriv_zero] at h
    calc
      _ = ‖a x‖ * ‖f x‖ := norm_mul _ _
      _ ≤ ‖a x‖ * (L * E x * m) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = _ := by dsimp [W0]; ring
  have hb2 (x : ℝ) : ‖iteratedDeriv 2 (a * f) x‖ ≤ W2 x * (L * m) := by
    rw [second_product a f ha hf x]
    have h0 := hfb 0 (by omega) x
    have h1 := hfb 1 (by omega) x
    have h2 := hfb 2 (by omega) x
    simp only [iteratedDeriv_zero, iteratedDeriv_one] at h0 h1
    calc
      _ ≤ ‖iteratedDeriv 2 a x * f x‖ + ‖2 * deriv a x * deriv f x‖ +
          ‖a x * iteratedDeriv 2 f x‖ := norm_add₃_le
      _ = ‖iteratedDeriv 2 a x‖ * ‖f x‖ + 2 * ‖deriv a x‖ * ‖deriv f x‖ +
          ‖a x‖ * ‖iteratedDeriv 2 f x‖ := by simp [norm_mul]
      _ ≤ ‖iteratedDeriv 2 a x‖ * (L * E x * m) +
          2 * ‖deriv a x‖ * (L * E x * m) + ‖a x‖ * (L * E x * m) := by
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 (norm_nonneg _))
          (mul_le_mul_of_nonneg_left h1 (by positivity)))
          (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
      _ = _ := by dsimp [W2]; simp only [iteratedDeriv_one]; ring
  have hi0 : (∫ x, ‖(a * f) x‖) ≤ (∫ x, W0 x) * (L * m) := by
    calc
      _ ≤ ∫ x, W0 x * (L * m) := integral_mono (by simpa using (hgi 0 (by omega)).norm)
        (hW0.mul_const _) hb0
      _ = _ := integral_mul_const _ _
  have hi2 : (∫ x, ‖iteratedDeriv 2 (a * f) x‖) ≤ (∫ x, W2 x) * (L * m) := by
    calc
      _ ≤ ∫ x, W2 x * (L * m) := integral_mono (hgi 2 (by omega)).norm (hW2.mul_const _) hb2
      _ = _ := integral_mul_const _ _
  obtain ⟨hfour, hfourb⟩ := fourier_c2_l1_bound (a * f) hg hgi
  rw [heq]
  refine ⟨by simpa using hgi 0 (by omega), hfour, ?_⟩
  calc
    _ ≤ ((∫ x, ‖(a * f) x‖) + (∫ x, ‖iteratedDeriv 2 (a * f) x‖)) * J := hfourb
    _ ≤ ((∫ x, W0 x) * (L * m) + (∫ x, W2 x) * (L * m)) * J :=
      mul_le_mul_of_nonneg_right (add_le_add hi0 hi2) hJ
    _ ≤ (L * ((∫ x, W0 x) + (∫ x, W2 x)) * J + 1) * m := by nlinarith

theorem fourier_inversion {I : Type*} [Fintype I]
    (ξ : ℝ → ℝ) (hξ : IsCutoff ξ) (P : I → ℝ → ℂ)
    (hP : UniformLogBounds P) (i : I) (v : ℝ) (hv : 0 < v) (x : ℝ) :
    localizedProfile ξ (P i) v x =
      FourierTransformInv.fourierInv
        (FourierTransform.fourier (localizedProfile ξ (P i) v)) x := by
  obtain ⟨K, hK, hbound⟩ := uniform_fourier_l1 ξ hξ P hP 1 (by norm_num)
  obtain ⟨hf, hff, _⟩ := hbound i v hv
  have heq : localizedProfile ξ (P i) v =
      fun x => (ξ x : ℂ) * logProfile (P i) (Real.log v + x) := by
    funext x
    simp [localizedProfile, logProfile, Real.exp_add, Real.exp_log hv]
  have hcont : Continuous (localizedProfile ξ (P i) v) := by
    rw [heq]
    exact (Complex.continuous_ofReal.comp hξ.1.continuous).mul
      ((hP.1 i).continuous.comp (continuous_const.add continuous_id))
  exact (hf.fourierInv_fourier_eq hff hcont.continuousAt).symm

theorem dyadic_log_mem (C D qc qd : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hc : C ≤ qc ∧ qc < 2 * C) (hd : D ≤ qd ∧ qd < 2 * D) :
    Real.log (qc / C) - 2 * Real.log (qd / D) ∈
      Set.Icc (-2 * Real.log 2) (Real.log 2) := by
  have hqc : 0 < qc := lt_of_lt_of_le hC hc.1
  have hqd : 0 < qd := lt_of_lt_of_le hD hd.1
  have hc1 : 1 ≤ qc / C := (le_div_iff₀ hC).2 (by simpa using hc.1)
  have hd1 : 1 ≤ qd / D := (le_div_iff₀ hD).2 (by simpa using hd.1)
  have hc2 : qc / C ≤ 2 := (div_le_iff₀ hC).2 hc.2.le
  have hd2 : qd / D ≤ 2 := (div_le_iff₀ hD).2 hd.2.le
  have hlc0 : 0 ≤ Real.log (qc / C) := Real.log_nonneg hc1
  have hld0 : 0 ≤ Real.log (qd / D) := Real.log_nonneg hd1
  have hlc2 : Real.log (qc / C) ≤ Real.log 2 :=
    Real.log_le_log (div_pos hqc hC) hc2
  have hld2 : Real.log (qd / D) ≤ Real.log 2 :=
    Real.log_le_log (div_pos hqd hD) hd2
  constructor <;> linarith

theorem dyadic_separation {I : Type*} [Fintype I]
    (ξ : ℝ → ℝ) (hξ : IsCutoff ξ) (P : I → ℝ → ℂ)
    (hP : UniformLogBounds P) (i : I) (v C D qc qd : ℝ)
    (hv : 0 < v) (hC : 0 < C) (hD : 0 < D)
    (hc : C ≤ qc ∧ qc < 2 * C) (hd : D ≤ qd ∧ qd < 2 * D) :
    Integrable (fun t : ℝ =>
      FourierTransform.fourier (localizedProfile ξ (P i) v) t *
        normPhase t (qc / C) * normPhase (-2 * t) (qd / D)) ∧
    P i (v * (qc / C) / (qd / D) ^ 2) =
      ∫ t : ℝ, FourierTransform.fourier (localizedProfile ξ (P i) v) t *
        normPhase t (qc / C) * normPhase (-2 * t) (qd / D) := by
  have hqc : 0 < qc := lt_of_lt_of_le hC hc.1
  have hqd : 0 < qd := lt_of_lt_of_le hD hd.1
  have hr : 0 < qc / C := div_pos hqc hC
  have hs : 0 < qd / D := div_pos hqd hD
  let x := Real.log (qc / C) - 2 * Real.log (qd / D)
  let f := FourierTransform.fourier (localizedProfile ξ (P i) v)
  have hphase (t : ℝ) :
      Complex.exp ((2 * Real.pi * (t * x) : ℝ) * Complex.I) =
        normPhase t (qc / C) * normPhase (-2 * t) (qd / D) := by
    rw [normPhase, normPhase, ← Complex.exp_add]
    congr 1
    push_cast
    dsimp [x]
    push_cast
    ring
  have hcontphase (r : ℝ) : Continuous (fun t => normPhase t r) := by
    unfold normPhase
    fun_prop
  obtain ⟨K, hK, hbound⟩ := uniform_fourier_l1 ξ hξ P hP 1 (by norm_num)
  have hf : Integrable f := (hbound i v hv).2.1
  have hfirst : Integrable (fun t => f t * normPhase t (qc / C)) :=
    hf.mul_bdd (hcontphase _).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => (norm_normPhase t _ hr).le))
  have hall : Integrable
      (fun t => f t * normPhase t (qc / C) * normPhase (-2 * t) (qd / D)) :=
    hfirst.mul_bdd ((hcontphase _).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => (norm_normPhase (-2 * t) _ hs).le))
  refine ⟨hall, ?_⟩
  have hcut : ξ x = 1 := hξ.2.2 (dyadic_log_mem C D qc qd hC hD hc hd)
  have hexp : Real.exp x = (qc / C) / (qd / D) ^ 2 := by
    simp only [x, Real.exp_sub, Real.exp_log hr]
    rw [mul_comm (2 : ℝ), Real.exp_mul, Real.exp_log hs]
    norm_num
  have hinv := fourier_inversion ξ hξ P hP i v hv x
  rw [localizedProfile, hcut, Complex.ofReal_one, one_mul, hexp] at hinv
  convert hinv using 1
  · congr 1
    ring
  · rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [real_inner_comm, RCLike.inner_apply, conj_trivial, smul_eq_mul]
    rw [mul_comm x t, hphase]
    ring

end
end DedekindZetaZeroFree.RMFourierProfile
