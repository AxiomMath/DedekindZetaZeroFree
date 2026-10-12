module

public import DedekindZetaZeroFree.Eisenstein.Induction.ScatteringChamberAndSmoothTorusFibers

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory Filter Complex

namespace DedekindZetaZeroFree.KPLiteralScatteringGlobalContinuation
open KPLiteralRaw

private lemma exp_derivative_bound (x y l r : ℝ) (hr : 0 < r)
    (hxy : |x - y| < r) :
    |l| * Real.exp (x * l) ≤ r⁻¹ *
      (Real.exp ((y + 2 * r) * l) + Real.exp ((y - 2 * r) * l)) := by
  have hi : 0 ≤ r⁻¹ := le_of_lt (inv_pos.mpr hr)
  have hb : |l| * Real.exp (x * l) ≤ r⁻¹ * Real.exp (x * l + r * |l|) := by
    have hl : |l| ≤ r⁻¹ * Real.exp (r * |l|) := by
      have h := Real.add_one_le_exp (r * |l|)
      have h' : r * |l| ≤ Real.exp (r * |l|) := by linarith
      have h'' : |l| ≤ Real.exp (r * |l|) / r :=
        (le_div_iff₀ hr).2 (by simpa [mul_comm] using h')
      simpa [div_eq_mul_inv, mul_comm] using h''
    calc
      _ ≤ (r⁻¹ * Real.exp (r * |l|)) * Real.exp (x * l) :=
        mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le
      _ = r⁻¹ * Real.exp (x * l + r * |l|) := by rw [Real.exp_add]; ring
  rcases le_total 0 l with hl | hl
  · rw [abs_of_nonneg hl] at hb ⊢
    have hx : x ≤ y + r := by have := (abs_lt.mp hxy).2; linarith
    calc
      _ ≤ r⁻¹ * Real.exp (x * l + r * l) := hb
      _ ≤ r⁻¹ * Real.exp ((y + 2 * r) * l) := by
        gcongr
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.exp_pos _).le) hi
  · rw [abs_of_nonpos hl] at hb ⊢
    have hx : y - r ≤ x := by have := (abs_lt.mp hxy).1; linarith
    calc
      _ ≤ r⁻¹ * Real.exp (x * l + r * -l) := hb
      _ ≤ r⁻¹ * Real.exp ((y - 2 * r) * l) := by
        gcongr
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.exp_pos _).le) hi

lemma exponential_integral_differentiable
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (l : X → ℝ) (c : X → ℂ)
    (b : ℝ) (hint : ∀ s : ℂ, b < s.re →
      Integrable (fun a => Complex.exp (s * (l a : ℂ)) * c a) μ) :
    DifferentiableOn ℂ (fun s => ∫ a, Complex.exp (s * (l a : ℂ)) * c a ∂μ)
      {s : ℂ | b < s.re} := by
  intro z hz
  change b < z.re at hz
  let F : ℂ → X → ℂ := fun s a => Complex.exp (s * (l a : ℂ)) * c a
  let F' : ℂ → X → ℂ := fun s a => (l a : ℂ) * F s a
  have hd (s : ℂ) (a : X) : HasDerivAt (fun t => F t a) (F' s a) s := by
    dsimp [F, F']
    convert ((Complex.hasDerivAt_exp (s * (l a : ℂ))).comp s
      ((hasDerivAt_id s).mul_const (l a : ℂ))).mul_const (c a) using 1
    · ext t; simp [mul_comm]
    · ring
  have hm : AEStronglyMeasurable (F' z) μ := by
    let q : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1)
    have hq : Tendsto q atTop (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, .of_forall ?_⟩
      intro n
      simp only [q, Set.mem_compl_iff, Set.mem_singleton_iff, one_div, inv_eq_zero]
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      exact_mod_cast hn
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n a => (q n)⁻¹ • (F (z + q n) a - F z a))
    · intro n
      change AEStronglyMeasurable ((q n)⁻¹ • (fun a => F (z + q n) a - F z a)) μ
      apply AEStronglyMeasurable.const_smul
      apply AEStronglyMeasurable.sub _ (hint z hz).aestronglyMeasurable
      apply (hint (z + q n) ?_).aestronglyMeasurable
      have hqpos : 0 < (q n).re := by
        simp [q, Complex.normSq]
        positivity
      simp only [Complex.add_re]
      linarith
    · exact ae_of_all μ fun a => (hd z a).tendsto_slope_zero.comp hq
  let r : ℝ := (z.re - b) / 4
  have hr : 0 < r := by dsimp [r]; linarith
  have hp : b < (z + (2 * r : ℝ)).re := by simp only [add_re, ofReal_re]; linarith
  have hn : b < (z - (2 * r : ℝ)).re := by simp only [sub_re, ofReal_re]; dsimp [r]; linarith
  let B : X → ℝ := fun a => r⁻¹ * (‖F (z + (2 * r : ℝ)) a‖ + ‖F (z - (2 * r : ℝ)) a‖)
  have hB : Integrable B μ :=
    (((hint _ hp).norm).add ((hint _ hn).norm)).const_mul _
  have hball : ∀ s ∈ Metric.ball z r, b < s.re := by
    intro s hs
    have hnorm : |s.re - z.re| < r :=
      (abs_re_le_norm (s - z)).trans_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hs)
    have := (abs_lt.mp hnorm).1
    dsimp [r] at this
    linarith
  have hbnd : ∀ a s, s ∈ Metric.ball z r → ‖F' s a‖ ≤ B a := by
    intro a s hs
    have hnorm : |s.re - z.re| < r :=
      (abs_re_le_norm (s - z)).trans_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hs)
    have he := mul_le_mul_of_nonneg_right
      (exp_derivative_bound s.re z.re (l a) r hr hnorm) (norm_nonneg (c a))
    simpa [F', F, B, norm_mul, Complex.norm_exp, Complex.mul_re,
      mul_add, add_mul, mul_assoc, Real.norm_eq_abs] using he
  have hder := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := B) (Metric.ball_mem_nhds z hr)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds z hr)
      (fun s hs => (hint s (hball s hs)).aestronglyMeasurable))
    (hint z hz) hm (ae_of_all μ fun a s hs => hbnd a s hs) hB
    (ae_of_all μ fun a s _ => hd s a)).2
  exact hder.differentiableAt.differentiableWithinAt

end DedekindZetaZeroFree.KPLiteralScatteringGlobalContinuation

end
