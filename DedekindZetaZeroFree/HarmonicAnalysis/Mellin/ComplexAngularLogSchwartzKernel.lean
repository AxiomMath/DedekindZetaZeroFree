module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensityRegularity.Angular
noncomputable section
open MeasureTheory

def circleAverage (g : ℂ → ℂ) (t : ℝ) : ℂ :=
  ∫ θ : ℝ in Set.Icc 0 (2 * Real.pi),
    g ((Real.exp (t / 2) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))

def weightedCircleAverage (g : ℂ → ℂ) (σ t : ℝ) : ℂ :=
  ((Real.exp (σ * t) : ℂ) / 2) * circleAverage g t

def rawEulerOp (h : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  (1 / 2 : ℝ) • SchwartzMap.bilinLeftCLM
    (ContinuousLinearMap.apply (E := ℂ) ℝ ℂ).flip
    (Function.HasTemperateGrowth.id') (SchwartzMap.fderivCLM ℝ ℂ ℂ h)

@[simp] theorem rawEulerOp_apply (h : SchwartzMap ℂ ℂ) (z : ℂ) :
    rawEulerOp h z = (1 / 2 : ℝ) • fderiv ℝ h z z := rfl

def angPoint (a : ℝ) : ℂ := Complex.exp ((a : ℂ) * Complex.I)

private theorem continuous_angPoint : Continuous angPoint := by
  unfold angPoint; fun_prop

private theorem continuous_flow (h : SchwartzMap ℂ ℂ) (x : ℝ) :
    Continuous (fun a : ℝ => h (Real.exp (x / 2) • angPoint a)) :=
  h.continuous.comp
    ((continuous_const : Continuous (fun _ : ℝ => Real.exp (x / 2))).smul continuous_angPoint)

private theorem hasDerivAt_flow (h : SchwartzMap ℂ ℂ) (y : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => h (Real.exp (s / 2) • y))
      (rawEulerOp h (Real.exp (t / 2) • y)) t := by
  have hz : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) / 2) t := by
    have h1 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id t).div_const 2
    simpa only [div_eq_mul_inv, one_mul] using h1.exp
  have hinner : HasDerivAt (fun s : ℝ => Real.exp (s / 2) • y)
      ((Real.exp (t / 2) / 2) • y) t := hz.smul_const y
  have houter : HasFDerivAt (fun z : ℂ => h z) (fderiv ℝ h (Real.exp (t / 2) • y))
      (Real.exp (t / 2) • y) := h.hasFDerivAt _
  have hcomp := houter.comp_hasDerivAt t hinner
  have hkey : fderiv ℝ h (Real.exp (t / 2) • y) ((Real.exp (t / 2) / 2) • y)
      = rawEulerOp h (Real.exp (t / 2) • y) := by
    have hsplit : (Real.exp (t / 2) / 2) • y = (1 / 2 : ℝ) • (Real.exp (t / 2) • y) := by
      rw [smul_smul]; congr 1; ring
    rw [hsplit, map_smul, rawEulerOp_apply]
  simpa only [Function.comp_def, hkey] using hcomp

private theorem hasDerivAt_circleAverage (h : SchwartzMap ℂ ℂ) (t : ℝ) :
    HasDerivAt (circleAverage h) (circleAverage (rawEulerOp h) t) t := by
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Icc 0 (2 * Real.pi)))
    (F := fun x a => h (Real.exp (x / 2) • angPoint a))
    (F' := fun x a => rawEulerOp h (Real.exp (x / 2) • angPoint a))
    (s := Metric.ball t 1) (x₀ := t)
    (bound := fun _ => SchwartzMap.seminorm ℝ 0 0 (rawEulerOp h))
    (Metric.ball_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun x => (continuous_flow h x).aestronglyMeasurable)
    (Integrable.of_bound (continuous_flow h t).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun a => SchwartzMap.norm_le_seminorm ℝ h _))
    ((continuous_flow (rawEulerOp h) t).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun a x _ =>
      SchwartzMap.norm_le_seminorm ℝ (rawEulerOp h) _)
    (integrable_const _)
    (Filter.Eventually.of_forall fun a x _ => hasDerivAt_flow h (angPoint a) x)
  obtain ⟨-, hderiv⟩ := hmain
  have hfun : (fun n : ℝ => ∫ a, h (Real.exp (n / 2) • angPoint a)
      ∂(volume.restrict (Set.Icc 0 (2 * Real.pi)))) = circleAverage h := by
    funext n
    simp only [circleAverage, angPoint, Complex.real_smul]
  have hder : (∫ a, rawEulerOp h (Real.exp (t / 2) • angPoint a)
      ∂(volume.restrict (Set.Icc 0 (2 * Real.pi)))) = circleAverage (rawEulerOp h) t := by
    simp only [circleAverage, angPoint, Complex.real_smul]
  rw [hfun, hder] at hderiv
  exact hderiv

theorem circleAverage_contDiff_iteratedDeriv (g : SchwartzMap ℂ ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (circleAverage g) ∧
      ∀ (n : ℕ) (t : ℝ),
        iteratedDeriv n (circleAverage g) t =
          circleAverage (rawEulerOp^[n] g) t := by
  have hiter : ∀ n : ℕ,
      iteratedDeriv n (circleAverage g) = circleAverage (rawEulerOp^[n] g) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [Function.iterate_succ_apply']
      exact (hasDerivAt_circleAverage (rawEulerOp^[n] g) t).deriv
  have hdiff : ∀ h : SchwartzMap ℂ ℂ, Differentiable ℝ (circleAverage h) :=
    fun h _ => (hasDerivAt_circleAverage h _).differentiableAt
  have hcont : ∀ h : SchwartzMap ℂ ℂ, Continuous (circleAverage h) :=
    fun h => (hdiff h).continuous
  refine ⟨?_, fun n t => congr_fun (hiter n) t⟩
  rw [contDiff_infty]
  intro n
  rw [contDiff_nat_iff_iteratedDeriv]
  exact ⟨fun m _ => by rw [hiter m]; exact hcont _,
    fun m _ => by rw [hiter m]; exact hdiff _⟩

end
end DedekindZetaZeroFree.ProbeSheetLogDensityRegularity.Angular

end

section
namespace DedekindZetaZeroFree.ProbeSheetLogDensityRegularity.Angular
noncomputable section
open MeasureTheory

private theorem circleAverage_integrable (h : SchwartzMap ℂ ℂ) (t : ℝ) :
    Integrable (fun θ : ℝ => h ((Real.exp (t / 2) : ℂ) *
      Complex.exp ((θ : ℂ) * Complex.I))) (volume.restrict (Set.Icc 0 (2 * Real.pi))) := by
  apply Integrable.of_bound (C := SchwartzMap.seminorm ℝ 0 0 h)
  · apply Continuous.aestronglyMeasurable
    exact h.continuous.comp (by fun_prop)
  · exact Filter.Eventually.of_forall fun θ => SchwartzMap.norm_le_seminorm ℝ h _

private theorem circleAverage_linear (h : SchwartzMap ℂ ℂ) (σ t : ℝ) :
    circleAverage ((σ : ℂ) • h + rawEulerOp h) t =
      (σ : ℂ) * circleAverage h t + circleAverage (rawEulerOp h) t := by
  simp only [circleAverage, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [integral_add ((circleAverage_integrable h t).const_mul _) (circleAverage_integrable _ t),
    integral_const_mul]

private theorem weighted_hasDerivAt (h : SchwartzMap ℂ ℂ) (σ t : ℝ) :
    HasDerivAt (weightedCircleAverage h σ)
      (weightedCircleAverage ((σ : ℂ) • h + rawEulerOp h) σ t) t := by
  have hc := circleAverage_contDiff_iteratedDeriv h
  have hd : HasDerivAt (circleAverage h) (circleAverage (rawEulerOp h) t) t := by
    have he := hc.2 1 t
    simp only [iteratedDeriv_one, Function.iterate_one] at he
    rw [← he]
    exact (hc.1.differentiable (by simp)).differentiableAt.hasDerivAt
  have he : HasDerivAt (fun s : ℝ => (Real.exp (σ * s) : ℂ) / 2)
      ((σ : ℂ) * (Real.exp (σ * t) : ℂ) / 2) t := by
    convert (((hasDerivAt_id t).const_mul σ).exp.ofReal_comp).div_const (2 : ℂ) using 1 <;>
      simp [mul_comm]
  convert he.mul hd using 1
  · rfl
  · rw [weightedCircleAverage, circleAverage_linear]
    ring

private theorem weighted_iterate (h : SchwartzMap ℂ ℂ) (σ : ℝ) (n : ℕ) :
    iteratedDeriv n (weightedCircleAverage h σ) =
      weightedCircleAverage ((fun h : SchwartzMap ℂ ℂ => (σ : ℂ) • h + rawEulerOp h)^[n] h) σ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [Function.iterate_succ_apply']
    exact (weighted_hasDerivAt _ σ t).deriv

private theorem polynomial_exp_bound (k : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → x ^ k * Real.exp (-b * x) ≤ C := by
  refine ⟨(k.factorial : ℝ) / b ^ k, by positivity, ?_⟩
  intro x hx
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have he := Real.pow_div_factorial_le_exp (b * x) (mul_nonneg hb.le hx) k
  have he' : b ^ k * x ^ k ≤ Real.exp (b * x) * (k.factorial : ℝ) := by
    simpa only [mul_pow] using (div_le_iff₀ hf).mp he
  apply (le_div_iff₀ (pow_pos hb k)).mpr
  calc
    x ^ k * Real.exp (-b * x) * b ^ k =
        (b ^ k * x ^ k) * Real.exp (-(b * x)) := by ring
    _ ≤ (Real.exp (b * x) * (k.factorial : ℝ)) * Real.exp (-(b * x)) :=
      mul_le_mul_of_nonneg_right he' (Real.exp_pos _).le
    _ = k.factorial := by rw [mul_right_comm, ← Real.exp_add]; simp

private theorem weighted_norm_bound (h : SchwartzMap ℂ ℂ) (σ t : ℝ) (m : ℕ) :
    ‖weightedCircleAverage h σ t‖ ≤
      (SchwartzMap.seminorm ℝ m 0 h *
        (volume.restrict (Set.Icc 0 (2 * Real.pi))).real Set.univ / 2) *
          Real.exp ((σ - (m : ℝ) / 2) * t) := by
  have hp : ∀ θ : ℝ, ‖h ((Real.exp (t / 2) : ℂ) *
      Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
        SchwartzMap.seminorm ℝ m 0 h * Real.exp (-((m : ℝ) * (t / 2))) := by
    intro θ
    have hn : ‖(Real.exp (t / 2) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ =
        Real.exp (t / 2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      simp only [Complex.norm_exp_ofReal_mul_I, mul_one]
    have hs := SchwartzMap.norm_pow_mul_le_seminorm ℝ h m
      ((Real.exp (t / 2) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
    rw [hn, ← Real.exp_nat_mul] at hs
    have ht := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-((m : ℝ) * (t / 2)))).le
    have hc : Real.exp (-((m : ℝ) * (t / 2))) * Real.exp ((m : ℝ) * (t / 2)) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      ‖h ((Real.exp (t / 2) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ =
          Real.exp (-((m : ℝ) * (t / 2))) *
            (Real.exp ((m : ℝ) * (t / 2)) *
              ‖h ((Real.exp (t / 2) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) := by
        rw [← mul_assoc, hc, one_mul]
      _ ≤ _ := by simpa only [mul_comm (Real.exp (-((m : ℝ) * (t / 2))))] using ht
  have hi := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Set.Icc 0 (2 * Real.pi))) (Filter.Eventually.of_forall hp)
  change ‖circleAverage h t‖ ≤ _ at hi
  rw [weightedCircleAverage, norm_mul, norm_div]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_ofNat]
  calc
    Real.exp (σ * t) / 2 * ‖circleAverage h t‖ ≤
        Real.exp (σ * t) / 2 *
          (SchwartzMap.seminorm ℝ m 0 h * Real.exp (-((m : ℝ) * (t / 2))) *
            (volume.restrict (Set.Icc 0 (2 * Real.pi))).real Set.univ) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by
      have he : Real.exp (σ * t) * Real.exp (-((m : ℝ) * (t / 2))) =
          Real.exp ((σ - (m : ℝ) / 2) * t) := by rw [← Real.exp_add]; congr 1; ring
      calc
        _ = (SchwartzMap.seminorm ℝ m 0 h *
          (volume.restrict (Set.Icc 0 (2 * Real.pi))).real Set.univ / 2) *
          (Real.exp (σ * t) * Real.exp (-((m : ℝ) * (t / 2)))) := by ring
        _ = _ := by rw [he]

theorem weightedCircleAverage_iteratedDeriv_decay (g : SchwartzMap ℂ ℂ)
    (σ : ℝ) (hσ : 0 < σ) :
    ∀ (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ,
      ‖t‖ ^ k * ‖iteratedDeriv n (weightedCircleAverage g σ) t‖ ≤ C := by
  intro k n
  rw [weighted_iterate]
  generalize (fun h : SchwartzMap ℂ ℂ => (σ : ℂ) • h + rawEulerOp h)^[n] g = h
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * σ)
  have hb : 0 < (m : ℝ) / 2 - σ := by linarith
  obtain ⟨C₁, hC₁, hp₁⟩ := polynomial_exp_bound k σ hσ
  obtain ⟨C₂, hC₂, hp₂⟩ := polynomial_exp_bound k ((m : ℝ) / 2 - σ) hb
  let V := (volume.restrict (Set.Icc 0 (2 * Real.pi))).real Set.univ
  let A := SchwartzMap.seminorm ℝ 0 0 h * V / 2
  let B := SchwartzMap.seminorm ℝ m 0 h * V / 2
  have hA : 0 ≤ A := by dsimp [A, V]; positivity
  have hB : 0 ≤ B := by dsimp [B, V]; positivity
  refine ⟨A * C₁ + B * C₂, fun t => ?_⟩
  by_cases ht : 0 ≤ t
  · have he := weighted_norm_bound h σ t m
    have hp := hp₂ t ht
    rw [Real.norm_of_nonneg ht]
    calc
      t ^ k * ‖weightedCircleAverage h σ t‖ ≤
          t ^ k * (B * Real.exp ((σ - (m : ℝ) / 2) * t)) :=
        mul_le_mul_of_nonneg_left he (pow_nonneg ht k)
      _ = B * (t ^ k * Real.exp (-((m : ℝ) / 2 - σ) * t)) := by
        rw [show (σ - (m : ℝ) / 2) * t = -((m : ℝ) / 2 - σ) * t by ring]
        ring
      _ ≤ B * C₂ := mul_le_mul_of_nonneg_left hp hB
      _ ≤ A * C₁ + B * C₂ := le_add_of_nonneg_left (mul_nonneg hA hC₁)
  · have ht' : t ≤ 0 := le_of_not_ge ht
    have he := weighted_norm_bound h σ t 0
    simp only [Nat.cast_zero, zero_div, sub_zero] at he
    have hp := hp₁ (-t) (neg_nonneg.mpr ht')
    rw [Real.norm_of_nonpos ht']
    calc
      (-t) ^ k * ‖weightedCircleAverage h σ t‖ ≤
          (-t) ^ k * (A * Real.exp (σ * t)) :=
        mul_le_mul_of_nonneg_left he (pow_nonneg (neg_nonneg.mpr ht') k)
      _ = A * ((-t) ^ k * Real.exp (-σ * (-t))) := by rw [neg_mul_neg]; ring
      _ ≤ A * C₁ := mul_le_mul_of_nonneg_left hp hA
      _ ≤ A * C₁ + B * C₂ := le_add_of_nonneg_right (mul_nonneg hB hC₂)

end
end DedekindZetaZeroFree.ProbeSheetLogDensityRegularity.Angular

end

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensityRegularity
noncomputable section
open MeasureTheory

def rawComplexAngularLogKernel (g : ℂ → ℂ) (σ t : ℝ) : ℂ :=
  ((Real.exp (σ * t) : ℂ) / 2) *
    ∫ θ : ℝ in Set.Icc 0 (2 * Real.pi),
      g ((Real.exp (t / 2) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))

theorem complex_angular_log_kernel_isSchwartz (g : SchwartzMap ℂ ℂ)
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ k : SchwartzMap ℝ ℂ, ∀ t, k t = rawComplexAngularLogKernel g σ t := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (Angular.weightedCircleAverage g σ) := by
    unfold Angular.weightedCircleAverage
    apply ContDiff.mul
    · have he : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.exp (σ * t)) := by
        fun_prop
      exact (Complex.ofRealCLM.contDiff.comp he).div_const (2 : ℂ)
    · exact (Angular.circleAverage_contDiff_iteratedDeriv g).1
  have hd : ∀ k n : ℕ, ∃ C : ℝ, ∀ t : ℝ,
      ‖t‖ ^ k * ‖iteratedFDeriv ℝ n (Angular.weightedCircleAverage g σ) t‖ ≤ C := by
    intro k n
    obtain ⟨C, hC⟩ := Angular.weightedCircleAverage_iteratedDeriv_decay g σ hσ k n
    refine ⟨C, fun t => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hC t
  refine ⟨⟨Angular.weightedCircleAverage g σ, hs, hd⟩, fun t => ?_⟩
  rfl

end
end DedekindZetaZeroFree.ProbeSheetLogDensityRegularity

end
