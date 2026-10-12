module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LogarithmicWeights

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped Classical

namespace DedekindZetaZeroFree.LargeSieve.Vendor

private lemma laplace_integrable (k : ℕ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^k * Complex.exp (-s * t)) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-s.re * t) • t^k) (Ici 0) :=
    integrableOn_exp_neg_smul_of_isBigO_exp
      ((show Continuous (fun t : ℝ => t^k) by fun_prop).continuousOn.locallyIntegrableOn measurableSet_Ici)
      (isLittleO_pow_exp_pos_mul_atTop k (half_pos hs)).isBigO (by linarith)
  have heq : (fun t : ℝ => ‖(t : ℂ)^k * Complex.exp (-s * t)‖) =ᶠ[ae (volume.restrict (Ioi 0))]
      (fun t : ℝ => Real.exp (-s.re * t) • t^k) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp [norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, abs_of_pos (mem_Ioi.mp ht), mul_comm]
  exact (integrable_norm_iff (by fun_prop)).mp ((hi.mono_set Ioi_subset_Ici_self).congr heq.symm)

private lemma laplace_tendsto (k : ℕ) (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun t : ℝ => (t : ℂ)^k * Complex.exp (-s * t)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) s.re hs
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp [norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, abs_of_pos ht, Real.rpow_natCast]

private lemma laplace_integral (k : ℕ) (s : ℂ) (hs : 0 < s.re) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ)^k * Complex.exp (-s * t)) = (k.factorial : ℂ) / s^(k+1) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  induction k with
  | zero =>
    simpa [div_eq_mul_inv] using integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0
  | succ k ih =>
    have h := integral_Ioi_mul_deriv_eq_deriv_mul
      (u := fun t : ℝ => (t : ℂ)^(k+1))
      (u' := fun t : ℝ => ((k+1 : ℕ) : ℂ) * (t : ℂ)^k)
      (v := fun t : ℝ => Complex.exp (-s * t))
      (v' := fun t : ℝ => -s * Complex.exp (-s * t))
      (a := 0) (a' := 0) (b' := 0)
      (fun t ht => by simpa [Pi.pow_apply] using ((hasDerivAt_id t).ofReal_comp).fun_pow (k+1))
      (fun t ht => by simpa [mul_comm] using (((hasDerivAt_id t).ofReal_comp).const_mul (-s)).cexp)
      (by simpa only [Pi.mul_def, IntegrableOn, mul_left_comm _ (-s)] using (laplace_integrable (k+1) s hs).const_mul (-s))
      (by simpa only [Pi.mul_def, IntegrableOn, mul_assoc] using (laplace_integrable k s hs).const_mul ((k+1 : ℕ) : ℂ))
      (by simpa [Pi.mul_def] using ((show Continuous (fun t : ℝ => (t : ℂ)^(k+1) * Complex.exp (-s*t)) by fun_prop).tendsto 0).mono_left nhdsWithin_le_nhds)
      (laplace_tendsto (k+1) s hs)
    have he : (∫ t in Ioi (0 : ℝ), (t : ℂ)^(k+1) * (-s * Complex.exp (-s*t))) =
        -s * (∫ t in Ioi (0 : ℝ), (t : ℂ)^(k+1) * Complex.exp (-s*t)) := by
      rw [← integral_const_mul]; congr 1; funext t; ring
    rw [he] at h
    simp only [mul_assoc, integral_const_mul, ih] at h
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    apply (mul_left_cancel₀ (neg_ne_zero.mpr hs0))
    rw [h]
    field_simp
    <;> push_cast <;> ring
private lemma exp_neg_image : (fun t : ℝ => Real.exp (-t)) '' Ioi 0 = Ioo 0 1 := by
  rw [show (fun t : ℝ => Real.exp (-t)) = Real.exp ∘ Neg.neg from rfl, image_comp]
  rw [image_neg_Ioi, neg_zero, Real.image_exp_Iio, Real.exp_zero]

private lemma exp_neg_subst (k : ℕ) (s : ℂ) (t : ℝ) :
    |-Real.exp (-t)| • ((Real.exp (-t) : ℂ)^(s-1) * (Real.log (Real.exp (-t)) : ℂ)^k) =
      (-1 : ℂ)^k * ((t : ℂ)^k * Complex.exp (-s*t)) := by
  rw [abs_neg, abs_of_pos (Real.exp_pos _), Real.log_exp, Complex.ofReal_neg, neg_pow,
    Complex.real_smul]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_exp]
  have he : Complex.exp ↑(-t) * Complex.exp (↑(-t) * (s-1)) = Complex.exp (-s*t) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (-1 : ℂ)^k * ((t : ℂ)^k * (Complex.exp ↑(-t) * Complex.exp (↑(-t) * (s-1)))) := by ring
    _ = _ := by rw [he]

theorem logMonomial_integrableOn (k : ℕ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * (Real.log x : ℂ) ^ k)
      (Set.Ioo 0 1) := by
  rw [← exp_neg_image]
  apply (integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun t ht => ((hasDerivAt_neg t).exp).hasDerivWithinAt)
    (fun x hx y hy h => neg_injective (Real.exp_injective h)) _).mpr
  simpa only [mul_neg_one, exp_neg_subst, IntegrableOn] using (laplace_integrable k s hs).const_mul ((-1 : ℂ)^k)

theorem integral_logMonomial (k : ℕ) (s : ℂ) (hs : 0 < s.re) :
    (∫ x in Set.Ioo (0 : ℝ) 1, (x : ℂ) ^ (s - 1) * (Real.log x : ℂ) ^ k) =
      (-1 : ℂ) ^ k * (k.factorial : ℂ) / s ^ (k + 1) := by
  rw [← exp_neg_image, integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun t ht => ((hasDerivAt_neg t).exp).hasDerivWithinAt)
    (fun x hx y hy h => neg_injective (Real.exp_injective h))]
  simp_rw [mul_neg_one, exp_neg_subst]
  rw [integral_const_mul, laplace_integral k s hs, mul_div_assoc]

private lemma poly_integrable (P : Polynomial ℂ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^(s-1)*P.eval (Real.log x : ℂ)) (Ioo 0 1) := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  apply integrable_finsetSum
  intro k hk
  simpa only [mul_left_comm] using (logMonomial_integrableOn k s hs).const_mul (P.coeff k)

def truncatedLogPolynomial (P : Polynomial ℂ) (x : ℝ) : ℂ :=
  if 0 < x ∧ x < 1 then P.eval (Real.log x : ℂ) else 0

private lemma truncated_weight (P : Polynomial ℂ) (s : ℂ) :
    (fun x : ℝ => (x : ℂ)^(s-1)*truncatedLogPolynomial P x) =
    (Ioo 0 1).indicator (fun x : ℝ => (x : ℂ)^(s-1)*P.eval (Real.log x : ℂ)) := by
  funext x
  simp only [truncatedLogPolynomial, Set.indicator, mem_Ioo]
  split_ifs <;> simp

theorem truncatedLogPolynomial_mellinConvergent (P : Polynomial ℂ) (s : ℂ)
    (hs : 0 < s.re) : MellinConvergent (truncatedLogPolynomial P) s := by
  unfold MellinConvergent
  simp only [smul_eq_mul, truncated_weight]
  exact ((integrable_indicator_iff measurableSet_Ioo).mpr (poly_integrable P s hs)).integrableOn

theorem mellin_truncatedLogPolynomial (P : Polynomial ℂ) (s : ℂ) (hs : 0 < s.re) :
    mellin (truncatedLogPolynomial P) s = logPrincipalPart P s := by
  unfold mellin
  simp only [smul_eq_mul, truncated_weight]
  rw [setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun x hx => hx.1)]
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  rw [integral_finsetSum]
  · unfold logPrincipalPart
    apply Finset.sum_congr rfl
    intro k hk
    rw [show (fun x : ℝ => (x : ℂ)^(s-1)*(P.coeff k*(Real.log x : ℂ)^k)) =
      (fun x : ℝ => P.coeff k*((x : ℂ)^(s-1)*(Real.log x : ℂ)^k)) by funext x; ring,
      integral_const_mul, integral_logMonomial k s hs]
    ring
  · intro k hk
    simpa only [mul_left_comm] using (logMonomial_integrableOn k s hs).const_mul (P.coeff k)

end DedekindZetaZeroFree.LargeSieve.Vendor

end
