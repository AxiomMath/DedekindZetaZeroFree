module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

@[expose] public section

namespace DedekindZetaZeroFree.ProbeSheetLogDensityRegularity
noncomputable section

def rawRealSignedLogKernel (g : ℝ → ℂ) (σ t : ℝ) : ℂ :=
  ((Real.exp (σ * t) : ℂ) / 2) *
    (g (Real.exp (t / 2)) + g (-Real.exp (t / 2)))

def logKernel (g : SchwartzMap ℝ ℂ) (σ : ℝ) : ℝ → ℂ :=
  fun t => g (Real.exp (t / 2)) * (Real.exp (σ * t) : ℂ)

def euler (g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (1 / 2 : ℝ) • SchwartzMap.smulLeftCLM ℂ
    (fun x : ℝ => (x : ℂ)) (SchwartzMap.derivCLM ℂ ℂ g)

@[simp] private theorem euler_apply (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    euler g x = (1 / 2 : ℝ) • ((x : ℂ) * deriv g x) := by
  unfold euler
  rw [SchwartzMap.smul_apply]
  rw [SchwartzMap.smulLeftCLM_apply
    (show Function.HasTemperateGrowth (fun x : ℝ => (x : ℂ)) from
      Complex.ofRealCLM.hasTemperateGrowth)]
  rfl

private theorem logKernel_contDiff (g : SchwartzMap ℝ ℂ) (σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (logKernel g σ) := by
  unfold logKernel
  apply ContDiff.mul
  · exact g.smooth'.comp (by fun_prop)
  · have he : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.exp (σ * t)) := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp he

private theorem hasDerivAt_logFlow (g : SchwartzMap ℝ ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => g (Real.exp (u / 2)))
      (euler g (Real.exp (t / 2))) t := by
  have he : HasDerivAt (fun u : ℝ => Real.exp (u / 2))
      (Real.exp (t / 2) / 2) t := by
    simpa [div_eq_mul_inv] using ((hasDerivAt_id t).div_const 2).exp
  convert g.differentiableAt.hasFDerivAt.comp_hasDerivAt t he using 1
  · rfl
  · rw [euler_apply, fderiv_eq_smul_deriv]
    simp [smul_eq_mul]
    ring

private theorem iteratedDeriv_logFlow (g : SchwartzMap ℝ ℂ) (n : ℕ) :
    iteratedDeriv n (fun u : ℝ => g (Real.exp (u / 2))) =
      fun u => (euler^[n] g) (Real.exp (u / 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [(hasDerivAt_logFlow (euler^[n] g) t).deriv]
    simp only [Function.iterate_succ_apply']

private theorem iteratedDeriv_expWeight (σ : ℝ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => (Real.exp (σ * t) : ℂ)) =
      fun t => (σ : ℂ) ^ n * (Real.exp (σ * t) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd := (((hasDerivAt_id t).const_mul σ).exp.ofReal_comp).const_mul
      ((σ : ℂ) ^ n)
    convert hd.deriv using 1 <;>
      simp only [pow_succ, Complex.ofReal_mul, id_eq, mul_one] <;> ring

private theorem iteratedDeriv_logKernel (g : SchwartzMap ℝ ℂ) (σ : ℝ) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (logKernel g σ) t =
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * (σ : ℂ) ^ (n - i) * logKernel (euler^[i] g) σ t := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => g (Real.exp (t / 2))) :=
    g.smooth'.comp (by fun_prop)
  have hw : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (Real.exp (σ * t) : ℂ)) := by
    have he : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.exp (σ * t)) := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp he
  change iteratedDeriv n (fun u : ℝ => g (Real.exp (u / 2)) *
      (Real.exp (σ * u) : ℂ)) t = _
  rw [iteratedDeriv_fun_mul (hf.of_le (by simp)).contDiffAt
    (hw.of_le (by simp)).contDiffAt]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_logFlow, iteratedDeriv_expWeight]
  dsimp [logKernel]
  ring

private lemma pow_mul_exp_neg_le_const {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, 0 ≤ s → s ^ k * Real.exp (-(c * s)) ≤ B := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    refine ⟨1, zero_le_one, fun s hs => ?_⟩
    rw [pow_zero, one_mul]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hc.le hs))
  · refine ⟨(k / (c * Real.exp 1)) ^ k, by positivity, fun s hs => ?_⟩
    have hy : (c * s / k) * Real.exp (-(c * s / k)) ≤ Real.exp (-1) :=
      Real.mul_exp_neg_le_exp_neg_one _
    have hbase : s * Real.exp (-(c * s / k)) ≤ k / (c * Real.exp 1) := by
      have h1 : (k / c) * ((c * s / k) * Real.exp (-(c * s / k))) ≤
          (k / c) * Real.exp (-1) :=
        mul_le_mul_of_nonneg_left hy (by positivity)
      have h2 : (k / c) * ((c * s / k) * Real.exp (-(c * s / k))) =
          s * Real.exp (-(c * s / k)) := by
        have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
        field_simp
      have h3 : (k / c) * Real.exp (-1) = k / (c * Real.exp 1) := by
        rw [Real.exp_neg]
        ring_nf
      rwa [h2, h3] at h1
    calc s ^ k * Real.exp (-(c * s))
        = (s * Real.exp (-(c * s / k))) ^ k := by
          rw [mul_pow, ← Real.exp_nat_mul]
          have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
          congr 1
          field_simp
      _ ≤ (k / (c * Real.exp 1)) ^ k := pow_le_pow_left₀ (by positivity) hbase k

private theorem logKernel_pow_bound (g : SchwartzMap ℝ ℂ) (σ : ℝ) (hσ : 0 < σ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ^ k * ‖logKernel g σ t‖ ≤ C := by
  obtain ⟨Bpos, hBposnn, hBpos⟩ := pow_mul_exp_neg_le_const (c := 1) one_pos k
  obtain ⟨Bneg, hBnegnn, hBneg⟩ := pow_mul_exp_neg_le_const (c := σ) hσ k
  obtain ⟨m, hm⟩ := exists_nat_ge (2 * (σ + 1))
  obtain ⟨C₀, hC₀pos, hC₀⟩ := g.decay 0 0
  obtain ⟨C₁, hC₁pos, hC₁⟩ := g.decay m 0
  have hC₀' : ∀ x, ‖g x‖ ≤ C₀ := by
    intro x
    simpa [norm_iteratedFDeriv_zero] using hC₀ x
  have hC₁' : ∀ x, ‖x‖ ^ m * ‖g x‖ ≤ C₁ := by
    intro x
    simpa [norm_iteratedFDeriv_zero] using hC₁ x
  have hnorm : ∀ t : ℝ, ‖logKernel g σ t‖ =
      ‖g (Real.exp (t / 2))‖ * Real.exp (σ * t) := by
    intro t
    simp only [logKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hσm : σ - (m : ℝ) / 2 ≤ -1 := by
    have hm' : (2 : ℝ) * (σ + 1) ≤ (m : ℝ) := hm
    linarith
  refine ⟨max (C₁ * Bpos) (C₀ * Bneg), le_max_of_le_left (by positivity), fun t => ?_⟩
  rw [hnorm t]
  by_cases ht : t ≤ 0
  · have ht' : 0 ≤ -t := by linarith
    have habs : |t| ^ k = (-t) ^ k := by rw [abs_of_nonpos ht]
    rw [habs]
    calc (-t) ^ k * (‖g (Real.exp (t / 2))‖ * Real.exp (σ * t))
        ≤ (-t) ^ k * (C₀ * Real.exp (σ * t)) := by
          gcongr
          exact hC₀' _
      _ = C₀ * ((-t) ^ k * Real.exp (σ * t)) := by ring
      _ = C₀ * ((-t) ^ k * Real.exp (-(σ * (-t)))) := by
          rw [show σ * t = -(σ * (-t)) by ring]
      _ ≤ C₀ * Bneg := mul_le_mul_of_nonneg_left (hBneg (-t) ht') hC₀pos.le
      _ ≤ max (C₁ * Bpos) (C₀ * Bneg) := le_max_right _ _
  · have ht0 : 0 ≤ t := le_of_lt (lt_of_not_ge ht)
    have habs : |t| ^ k = t ^ k := by rw [abs_of_nonneg ht0]
    have hpownorm : ‖Real.exp (t / 2)‖ ^ m = Real.exp ((m : ℝ) / 2 * t) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
      congr 1
      ring
    have hgb : ‖g (Real.exp (t / 2))‖ ≤ C₁ / Real.exp ((m : ℝ) / 2 * t) := by
      have h := hC₁' (Real.exp (t / 2))
      rw [hpownorm] at h
      exact (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa [mul_comm] using h)
    have key : (C₁ / Real.exp ((m : ℝ) / 2 * t)) * Real.exp (σ * t) =
        C₁ * Real.exp ((σ - (m : ℝ) / 2) * t) := by
      rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [habs]
    calc t ^ k * (‖g (Real.exp (t / 2))‖ * Real.exp (σ * t))
        ≤ t ^ k * ((C₁ / Real.exp ((m : ℝ) / 2 * t)) * Real.exp (σ * t)) := by
          gcongr
      _ = t ^ k * (C₁ * Real.exp ((σ - (m : ℝ) / 2) * t)) := by rw [key]
      _ = C₁ * (t ^ k * Real.exp ((σ - (m : ℝ) / 2) * t)) := by ring
      _ ≤ C₁ * (t ^ k * Real.exp (-t)) := by
          apply mul_le_mul_of_nonneg_left _ hC₁pos.le
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht0 k)
          exact Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ C₁ * Bpos :=
          mul_le_mul_of_nonneg_left (by simpa using hBpos t ht0) hC₁pos.le
      _ ≤ max (C₁ * Bpos) (C₀ * Bneg) := le_max_left _ _

private theorem logKernel_decay (g : SchwartzMap ℝ ℂ) (σ : ℝ) (hσ : 0 < σ) :
    ∀ k n : ℕ, ∃ C : ℝ, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (logKernel g σ) x‖ ≤ C := by
  intro k n
  have hb : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, |t| ^ k * ‖logKernel (euler^[i] g) σ t‖ ≤ C :=
    fun i => logKernel_pow_bound (euler^[i] g) σ hσ k
  choose C hCnn hC using hb
  refine ⟨∑ i ∈ Finset.range (n + 1), ‖(n.choose i : ℂ) * (σ : ℂ) ^ (n - i)‖ * C i,
    fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_logKernel]
  calc ‖x‖ ^ k * ‖∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * (σ : ℂ) ^ (n - i) * logKernel (euler^[i] g) σ x‖
      ≤ ‖x‖ ^ k * (∑ i ∈ Finset.range (n + 1),
          ‖(n.choose i : ℂ) * (σ : ℂ) ^ (n - i) * logKernel (euler^[i] g) σ x‖) := by
          gcongr
          exact norm_sum_le _ _
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ k *
          ‖(n.choose i : ℂ) * (σ : ℂ) ^ (n - i) * logKernel (euler^[i] g) σ x‖ := by
          rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range (n + 1), ‖(n.choose i : ℂ) * (σ : ℂ) ^ (n - i)‖ *
          (‖x‖ ^ k * ‖logKernel (euler^[i] g) σ x‖) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_mul]
          ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), ‖(n.choose i : ℂ) * (σ : ℂ) ^ (n - i)‖ * C i := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [Real.norm_eq_abs]
          exact hC i x

private theorem logKernel_isSchwartz (g : SchwartzMap ℝ ℂ) (σ : ℝ) (hσ : 0 < σ) :
    ∃ k : SchwartzMap ℝ ℂ, ∀ t, k t = logKernel g σ t :=
  ⟨⟨logKernel g σ, logKernel_contDiff g σ, logKernel_decay g σ hσ⟩, fun _ => rfl⟩

def negComp (g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) g

@[simp] private theorem negComp_apply (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    negComp g x = g (-x) := rfl

theorem real_signed_log_kernel_isSchwartz (g : SchwartzMap ℝ ℂ)
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ k : SchwartzMap ℝ ℂ, ∀ t, k t = rawRealSignedLogKernel g σ t := by
  obtain ⟨kA, hkA⟩ := logKernel_isSchwartz g σ hσ
  obtain ⟨kB, hkB⟩ := logKernel_isSchwartz (negComp g) σ hσ
  refine ⟨(1 / 2 : ℝ) • (kA + kB), fun t => ?_⟩
  rw [SchwartzMap.smul_apply]
  change (1 / 2 : ℝ) • (kA t + kB t) = rawRealSignedLogKernel g σ t
  rw [hkA t, hkB t]
  simp only [logKernel, rawRealSignedLogKernel, negComp_apply]
  rw [Algebra.smul_def, Complex.coe_algebraMap]
  push_cast
  ring

end
end DedekindZetaZeroFree.ProbeSheetLogDensityRegularity
