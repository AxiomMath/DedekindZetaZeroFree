module

public import DedekindZetaZeroFree.Metaplectic.Weil.Complex.DampedGaussianEvaluation

@[expose] public section

namespace DedekindZetaZeroFree.ComplexWeil

noncomputable section
open MeasureTheory Filter
open scoped Topology

def PK (β a : ℂ) (ε : ℝ) : ℂ :=
  ((‖β‖ * Real.pi / Real.sqrt (ε ^ 2 + 4 * Real.pi ^ 2 * ‖β * a‖ ^ 2) : ℝ) : ℂ)

def EK (β a u ξ : ℂ) (ε : ℝ) : ℂ :=
  -(Real.pi : ℂ) ^ 2 * ((β * u * ξ).re : ℂ) ^ 2 /
      ((ε : ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (‖β * a‖ : ℂ)) -
    (Real.pi : ℂ) ^ 2 * ((β * u * ξ).im : ℂ) ^ 2 /
      ((ε : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (‖β * a‖ : ℂ))

private lemma K_eq (β a u ξ : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0)
    (hu : ‖u‖ = 1) (hrot : β * a * u ^ 2 = (‖β * a‖ : ℂ))
    (ε : ℝ) (hε : 0 < ε) :
    K β ε a ξ = PK β a ε * Complex.exp (EK β a u ξ ε) := by
  simpa only [PK, EK] using damped_gaussian_evaluation β a ξ hβ ha ε hε u hu hrot

private lemma prefactor_le (β a : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0) (ε : ℝ) :
    ‖β‖ * Real.pi / Real.sqrt (ε ^ 2 + 4 * Real.pi ^ 2 * ‖β * a‖ ^ 2) ≤ 1 / (2 * ‖a‖) := by
  have hbn : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hr : 0 < ‖β * a‖ := by rw [norm_mul]; positivity
  have h2πr : 0 ≤ 2 * Real.pi * ‖β * a‖ := by positivity
  have hsq : (2 * Real.pi * ‖β * a‖) ^ 2 ≤ ε ^ 2 + 4 * Real.pi ^ 2 * ‖β * a‖ ^ 2 := by
    nlinarith [sq_nonneg ε]
  have hs : 2 * Real.pi * ‖β * a‖ ≤ Real.sqrt (ε ^ 2 + 4 * Real.pi ^ 2 * ‖β * a‖ ^ 2) := by
    rw [← Real.sqrt_sq h2πr]
    exact Real.sqrt_le_sqrt hsq
  have hnum : 0 ≤ ‖β‖ * Real.pi := by positivity
  calc ‖β‖ * Real.pi / Real.sqrt (ε ^ 2 + 4 * Real.pi ^ 2 * ‖β * a‖ ^ 2)
      ≤ ‖β‖ * Real.pi / (2 * Real.pi * ‖β * a‖) :=
        div_le_div_of_nonneg_left hnum (by positivity) hs
    _ = 1 / (2 * ‖a‖) := by
        rw [norm_mul]
        have hb0 : ‖β‖ ≠ 0 := ne_of_gt hbn
        have hp0 : Real.pi ≠ 0 := Real.pi_ne_zero
        have ha0 : ‖a‖ ≠ 0 := ne_of_gt han
        field_simp

private lemma re_div_nonneg (s : ℝ) (hs : 0 ≤ s) (b : ℂ) (hb : 0 ≤ b.re) :
    0 ≤ ((s : ℂ) / b).re := by
  rw [div_eq_mul_inv, Complex.re_ofReal_mul, Complex.inv_re, ← mul_div_assoc]
  exact div_nonneg (mul_nonneg hs hb) (Complex.normSq_nonneg b)

private lemma re_div_nonpos (s : ℝ) (hs : s ≤ 0) (b : ℂ) (hb : 0 ≤ b.re) :
    ((s : ℂ) / b).re ≤ 0 := by
  rw [div_eq_mul_inv, Complex.re_ofReal_mul, Complex.inv_re, ← mul_div_assoc]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hs hb)
    (Complex.normSq_nonneg b)

private lemma EK_re_le_zero (β a u ξ : ℂ) (ε : ℝ) (hε : 0 < ε) :
    (EK β a u ξ ε).re ≤ 0 := by
  have hM : 0 ≤ ((ε : ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (‖β * a‖ : ℂ)).re := by
    simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    linarith
  have hP : 0 ≤ ((ε : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (‖β * a‖ : ℂ)).re := by
    simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    linarith
  have h1 : ((-(Real.pi : ℂ) ^ 2 * ((β * u * ξ).re : ℂ) ^ 2 /
      ((ε : ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (‖β * a‖ : ℂ)))).re ≤ 0 := by
    have hz : -(Real.pi : ℂ) ^ 2 * ((β * u * ξ).re : ℂ) ^ 2 =
        ((-(Real.pi ^ 2 * (β * u * ξ).re ^ 2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hz]
    exact re_div_nonpos _ (by nlinarith [Real.pi_pos, sq_nonneg (β * u * ξ).re]) _ hM
  have h2 : 0 ≤ ((Real.pi : ℂ) ^ 2 * ((β * u * ξ).im : ℂ) ^ 2 /
      ((ε : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (‖β * a‖ : ℂ))).re := by
    have hz : (Real.pi : ℂ) ^ 2 * ((β * u * ξ).im : ℂ) ^ 2 =
        ((Real.pi ^ 2 * (β * u * ξ).im ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hz]
    exact re_div_nonneg _ (by positivity) _ hP
  simp only [EK, Complex.sub_re]
  linarith

theorem norm_K_le (β a : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (ξ : ℂ) :
    ‖K β ε a ξ‖ ≤ 1 / (2 * ‖a‖) := by
  obtain ⟨u, hu, hrot⟩ := exists_quadratic_unit β a hβ ha
  rw [K_eq β a u ξ hβ ha hu hrot ε hε, norm_mul, Complex.norm_exp]
  have hPnn : 0 ≤ ‖β‖ * Real.pi / Real.sqrt (ε ^ 2 + 4 * Real.pi ^ 2 * ‖β * a‖ ^ 2) := by
    positivity
  have hnorm : ‖PK β a ε‖ =
      ‖β‖ * Real.pi / Real.sqrt (ε ^ 2 + 4 * Real.pi ^ 2 * ‖β * a‖ ^ 2) := by
    show ‖((‖β‖ * Real.pi / Real.sqrt (ε ^ 2 + 4 * Real.pi ^ 2 * ‖β * a‖ ^ 2) : ℝ) : ℂ)‖ =
        ‖β‖ * Real.pi / Real.sqrt (ε ^ 2 + 4 * Real.pi ^ 2 * ‖β * a‖ ^ 2)
    exact (RCLike.norm_ofReal _).trans (abs_of_nonneg hPnn)
  rw [hnorm]
  have hexp : Real.exp (EK β a u ξ ε).re ≤ 1 :=
    Real.exp_le_one_iff.mpr (EK_re_le_zero β a u ξ ε hε)
  calc ‖β‖ * Real.pi / Real.sqrt (ε ^ 2 + 4 * Real.pi ^ 2 * ‖β * a‖ ^ 2) *
        Real.exp (EK β a u ξ ε).re
      ≤ ‖β‖ * Real.pi / Real.sqrt (ε ^ 2 + 4 * Real.pi ^ 2 * ‖β * a‖ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hexp hPnn
    _ = ‖β‖ * Real.pi / Real.sqrt (ε ^ 2 + 4 * Real.pi ^ 2 * ‖β * a‖ ^ 2) := mul_one _
    _ ≤ 1 / (2 * ‖a‖) := prefactor_le β a hβ ha ε

private lemma EK_continuous (β a u ξ : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0) :
    Continuous (EK β a u ξ) := by
  have hr : 0 < ‖β * a‖ := norm_pos_iff.mpr (mul_ne_zero hβ ha)
  have hm (ε : ℝ) : ((ε : ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (‖β * a‖ : ℂ)) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [Complex.mul_im, Complex.mul_re] at hi
    rcases hi with hi | hi
    · exact hβ hi
    · exact ha hi
  have hp (ε : ℝ) : ((ε : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (‖β * a‖ : ℂ)) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [Complex.mul_im, Complex.mul_re] at hi
    rcases hi with hi | hi
    · exact hβ hi
    · exact ha hi
  unfold EK
  fun_prop

private lemma PK_continuous (β a : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0) :
    Continuous (PK β a) := by
  have hr : 0 < ‖β * a‖ := norm_pos_iff.mpr (mul_ne_zero hβ ha)
  have hs (ε : ℝ) : Real.sqrt (ε ^ 2 + 4 * Real.pi ^ 2 * ‖β * a‖ ^ 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    positivity
  unfold PK
  fun_prop

private lemma PK_zero (β a : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0) :
    PK β a 0 = ((1 / (2 * ‖a‖) : ℝ) : ℂ) := by
  have hb0 : ‖β‖ ≠ 0 := norm_ne_zero_iff.mpr hβ
  have ha0 : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hs : 4 * Real.pi ^ 2 * ‖β * a‖ ^ 2 = (2 * Real.pi * ‖β * a‖) ^ 2 := by ring
  simp only [PK, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, hs,
    Real.sqrt_sq (by positivity : 0 ≤ 2 * Real.pi * ‖β * a‖)]
  congr 1
  rw [norm_mul]
  field_simp

private lemma EK_zero (β a u ξ : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0)
    (hrot : β * a * u ^ 2 = (‖β * a‖ : ℂ)) :
    EK β a u ξ 0 = (((2 * Real.pi * (β * (-ξ ^ 2 / (4 * a))).re : ℝ) : ℂ) * Complex.I) := by
  have hr : (‖β * a‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr (mul_ne_zero hβ ha))
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hRe : (β * (-ξ ^ 2 / (4 * a))).re =
      -(((β * u * ξ).re ^ 2 - (β * u * ξ).im ^ 2) / ‖β * a‖) / 4 := by
    rw [frequency_square_difference β a u ξ hβ ha hrot]
    have h : β * (-ξ ^ 2 / (4 * a)) = -(β * ξ ^ 2 / a) / 4 := by ring
    rw [h]
    simp
  rw [hRe]
  unfold EK
  push_cast
  simp only [Complex.ofReal_zero, zero_sub, zero_add]
  rw [div_neg_eq_neg_div, div_eq_mul_inv, div_eq_mul_inv]
  simp only [mul_inv_rev, Complex.inv_I]
  field_simp
  ring

theorem tendsto_K (β a : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0) (ξ : ℂ) :
    Tendsto (fun ε : ℝ => K β ε a ξ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((1 / (2 * ‖a‖) : ℝ) : ℂ) * psi β (-ξ ^ 2 / (4 * a)))) := by
  obtain ⟨u, hu, hrot⟩ := exists_quadratic_unit β a hβ ha
  have h : Tendsto (fun ε => PK β a ε * Complex.exp (EK β a u ξ ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (PK β a 0 * Complex.exp (EK β a u ξ 0))) :=
    ((PK_continuous β a hβ ha).continuousAt.tendsto.mul
      (Complex.continuous_exp.comp (EK_continuous β a u ξ hβ ha)).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  rw [PK_zero β a hβ ha, EK_zero β a u ξ hβ ha hrot] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (K_eq β a u ξ hβ ha hu hrot ε hε).symm

theorem norm_schwartz_mul_K_le (β a : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (f : SchwartzMap ℂ ℂ) (y z : ℂ) :
    ‖f z * K β ε a (y + z)‖ ≤ (1 / (2 * ‖a‖)) * ‖f z‖ := by
  rw [norm_mul, mul_comm (1 / (2 * ‖a‖))]
  exact mul_le_mul_of_nonneg_left (norm_K_le β a hβ ha ε hε (y + z)) (norm_nonneg _)

theorem integrable_schwartz_kernel_bound (β a : ℂ) (f : SchwartzMap ℂ ℂ) :
    Integrable (fun z : ℂ => (1 / (2 * ‖a‖)) * ‖f z‖) (mu β) := by
  exact (integrable_schwartz_mu β f).norm.const_mul _

theorem tendsto_integral_schwartz_mul_K (β a : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0)
    (f : SchwartzMap ℂ ℂ) (y : ℂ) :
    Tendsto (fun ε : ℝ => ∫ z : ℂ, f z * K β ε a (y + z) ∂mu β)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ z : ℂ, f z * ((1 / (2 * ‖a‖) : ℝ) : ℂ) *
        psi β (-(y + z) ^ 2 / (4 * a)) ∂mu β)) := by
  obtain ⟨u, hu, hrot⟩ := exists_quadratic_unit β a hβ ha
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z : ℂ => (1 / (2 * ‖a‖)) * ‖f z‖)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hc : Continuous (fun z : ℂ => f z * K β ε a (y + z)) := by
      have heq : (fun z : ℂ => f z * K β ε a (y + z)) =
          (fun z : ℂ => f z * (PK β a ε * Complex.exp (EK β a u (y + z) ε))) := by
        funext z
        rw [K_eq β a u (y + z) hβ ha hu hrot ε hε]
      rw [heq]
      unfold EK
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Filter.Eventually.of_forall (fun z => norm_schwartz_mul_K_le β a hβ ha ε hε f y z)
  · exact integrable_schwartz_kernel_bound β a f
  · exact Filter.Eventually.of_forall fun z => by
      simpa only [mul_assoc] using (tendsto_K β a hβ ha (y + z)).const_mul (f z)

end
end DedekindZetaZeroFree.ComplexWeil
