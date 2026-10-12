module

public import DedekindZetaZeroFree.Analysis.MellinVerticalIntegral

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Classical Topology

namespace DedekindZetaZeroFree.LargeSieve.Vendor

private lemma re_shift (a : ℝ) (t : ℝ) : (((a : ℂ) + (t : ℂ) * Complex.I).re) = a := by
  simp [Complex.add_re, Complex.mul_re]

private lemma im_shift (a : ℝ) (t : ℝ) : (((a : ℂ) + (t : ℂ) * Complex.I).im) = t := by
  simp [Complex.add_im, Complex.mul_im]

private lemma norm_lower (a : ℝ) (t : ℝ) :
    (1 + |t|) * |a| ≤ (1 + |a|) * ‖(a : ℂ) + (t : ℂ) * Complex.I‖ := by
  have ha : |a| ≤ ‖(a : ℂ) + (t : ℂ) * Complex.I‖ := by
    have h := Complex.abs_re_le_norm ((a : ℂ) + (t : ℂ) * Complex.I)
    rwa [re_shift] at h
  have ht : |t| ≤ ‖(a : ℂ) + (t : ℂ) * Complex.I‖ := by
    have h := Complex.abs_im_le_norm ((a : ℂ) + (t : ℂ) * Complex.I)
    rwa [im_shift] at h
  rcases le_total |t| |a| with h | h
  · have h1 : (1 + |t|) ≤ (1 + |a|) := by linarith
    have h2 : (1 + |t|) * |a| ≤ (1 + |a|) * |a| :=
      mul_le_mul_of_nonneg_right h1 (abs_nonneg a)
    have h3 : (1 + |a|) * |a| ≤ (1 + |a|) * ‖(a : ℂ) + (t : ℂ) * Complex.I‖ :=
      mul_le_mul_of_nonneg_left ha (by linarith [abs_nonneg a])
    linarith
  · have h2 : (1 + |t|) * |a| ≤ (1 + |a|) * |t| := by
      nlinarith [abs_nonneg a, abs_nonneg t]
    have h3 : (1 + |a|) * |t| ≤ (1 + |a|) * ‖(a : ℂ) + (t : ℂ) * Complex.I‖ :=
      mul_le_mul_of_nonneg_left ht (by linarith [abs_nonneg a])
    linarith

private lemma norm_zpow_bound (a : ℝ) (ha : a ≠ 0) {m : ℕ} (hm : 2 ≤ m) (t : ℝ) :
    ‖((a : ℂ) + (t : ℂ) * Complex.I) ^ (-(m : ℤ))‖ ≤
      ((1 + |a|) / |a|) ^ m * (1 + t ^ 2)⁻¹ := by
  set r : ℝ := ‖(a : ℂ) + (t : ℂ) * Complex.I‖ with hr
  have hapos : 0 < |a| := abs_pos.mpr ha
  have hrpos : 0 < r := by
    rw [hr]
    have h := Complex.abs_re_le_norm ((a : ℂ) + (t : ℂ) * Complex.I)
    rw [re_shift] at h
    exact lt_of_lt_of_le hapos h
  have hle : (1 + |t|) ≤ ((1 + |a|) / |a|) * r := by
    rw [hr]
    rw [div_mul_eq_mul_div, le_div_iff₀ hapos]
    linarith [norm_lower a t]
  have h1 : r⁻¹ ≤ ((1 + |a|) / |a|) * (1 + |t|)⁻¹ := by
    rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hrpos (by positivity)]
    linarith
  have h2 : (r⁻¹) ^ m ≤ (((1 + |a|) / |a|) * (1 + |t|)⁻¹) ^ m :=
    pow_le_pow_left₀ (inv_nonneg.mpr hrpos.le) h1 m
  have h3 : (1 + |t|) ^ (-(m : ℤ)) ≤ (1 + t ^ 2)⁻¹ := by
    have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ m := by
      have h2' : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t, sq_nonneg t]
      have h3' : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ m :=
        pow_le_pow_right₀ (by linarith [abs_nonneg t]) hm
      linarith
    rw [zpow_neg, zpow_natCast]
    simpa [one_div] using
      (one_div_le_one_div_of_le (show (0:ℝ) < 1 + t ^ 2 by positivity) hsq)
  have h4 : (((1 + |a|) / |a|) * (1 + |t|)⁻¹) ^ m =
      ((1 + |a|) / |a|) ^ m * (1 + |t|) ^ (-(m : ℤ)) := by
    rw [mul_pow, inv_pow, zpow_neg, zpow_natCast]
  calc ‖((a : ℂ) + (t : ℂ) * Complex.I) ^ (-(m : ℤ))‖
      = (r⁻¹) ^ m := by
        rw [hr, norm_zpow, zpow_neg, zpow_natCast, inv_pow]
    _ ≤ (((1 + |a|) / |a|) * (1 + |t|)⁻¹) ^ m := h2
    _ = ((1 + |a|) / |a|) ^ m * (1 + |t|) ^ (-(m : ℤ)) := h4
    _ ≤ ((1 + |a|) / |a|) ^ m * (1 + t ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

private lemma integrable_shift_zpow (a : ℝ) (ha : a ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    Integrable (fun t : ℝ => ((a : ℂ) + (t : ℂ) * Complex.I) ^ (-(m : ℤ))) volume := by
  have hne : ∀ t : ℝ, (a : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro t h
    have h2 := re_shift a t
    rw [h] at h2
    simp at h2
    exact ha h2.symm
  have hcont : Continuous (fun t : ℝ => ((a : ℂ) + (t : ℂ) * Complex.I) ^ (-(m : ℤ))) :=
    ((by fun_prop : Continuous fun t : ℝ => (a : ℂ) + (t : ℂ) * Complex.I)).zpow₀ _
      (fun t => Or.inl (hne t))
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (((1 + |a|) / |a|) ^ m))
    hcont.aestronglyMeasurable ?_
  exact Eventually.of_forall fun t => norm_zpow_bound a ha hm t

private lemma hasDerivAt_prim (a : ℝ) (ha : a ≠ 0) {m : ℕ} (hm : 2 ≤ m) (t : ℝ) :
    HasDerivAt (fun t : ℝ =>
        ((a : ℂ) + (t : ℂ) * Complex.I) ^ (1 - (m : ℤ)) *
          (Complex.I * ((1 - (m : ℤ) : ℤ) : ℂ))⁻¹)
      (((a : ℂ) + (t : ℂ) * Complex.I) ^ (-(m : ℤ))) t := by
  have hne : (a : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have h2 := re_shift a t
    rw [h] at h2
    simp at h2
    exact ha h2.symm
  have hu : HasDerivAt (fun t : ℝ => (a : ℂ) + (t : ℂ) * Complex.I) Complex.I t := by
    have h : HasDerivAt (fun w : ℂ => (a : ℂ) + w * Complex.I) (1 * Complex.I) (t : ℂ) :=
      ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).const_add (a : ℂ)
    simpa using h.comp_ofReal
  have hz := HasDerivAt.comp t (hasDerivAt_zpow (1 - (m : ℤ)) ((a : ℂ) + (t : ℂ) * Complex.I)
    (Or.inl hne)) hu
  have hz2 := hz.mul_const ((Complex.I * ((1 - (m : ℤ) : ℤ) : ℂ))⁻¹)
  refine hz2.congr_deriv ?_
  have hIn : Complex.I * ((1 - (m : ℤ) : ℤ) : ℂ) ≠ 0 := by
    refine mul_ne_zero Complex.I_ne_zero (fun h => ?_)
    have : (1 - (m : ℤ) : ℤ) = 0 := by exact_mod_cast h
    omega
  have h1 : ((1 - (m : ℤ) : ℤ) : ℂ) * ((a : ℂ) + (t : ℂ) * Complex.I) ^ ((1 - (m : ℤ)) - 1) *
        Complex.I * (Complex.I * ((1 - (m : ℤ) : ℤ) : ℂ))⁻¹ =
      ((a : ℂ) + (t : ℂ) * Complex.I) ^ ((1 - (m : ℤ)) - 1) *
        ((Complex.I * ((1 - (m : ℤ) : ℤ) : ℂ)) * (Complex.I * ((1 - (m : ℤ) : ℤ) : ℂ))⁻¹) := by
    ring
  rw [h1, mul_inv_cancel₀ hIn, mul_one]
  rw [show (1 - (m : ℤ)) - 1 = -(m : ℤ) by omega]

private lemma tendsto_prim_of (a : ℝ) {m : ℕ} {l : Filter ℝ}
    (hR : Tendsto (fun t : ℝ => ‖(a : ℂ) + (t : ℂ) * Complex.I‖) l atTop)
    (hn : (1 - (m : ℤ)) < 0) :
    Tendsto (fun t : ℝ => ((a : ℂ) + (t : ℂ) * Complex.I) ^ (1 - (m : ℤ)) *
        (Complex.I * ((1 - (m : ℤ) : ℤ) : ℂ))⁻¹) l (𝓝 0) := by
  have hpow : Tendsto (fun t : ℝ => ‖(a : ℂ) + (t : ℂ) * Complex.I‖ ^ (1 - (m : ℤ)))
      l (𝓝 0) := (tendsto_zpow_atTop_zero hn).comp hR
  have h2 : Tendsto (fun t : ℝ => ‖(a : ℂ) + (t : ℂ) * Complex.I‖ ^ (1 - (m : ℤ)) *
      ‖(Complex.I * ((1 - (m : ℤ) : ℤ) : ℂ))⁻¹‖) l (𝓝 0) := by
    simpa using hpow.mul_const ‖(Complex.I * ((1 - (m : ℤ) : ℤ) : ℂ))⁻¹‖
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (h2.congr' ?_)
  filter_upwards with t
  rw [norm_mul, norm_zpow]

private lemma tendsto_prim_atTop (a : ℝ) (ha : a ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun t : ℝ => ((a : ℂ) + (t : ℂ) * Complex.I) ^ (1 - (m : ℤ)) *
        (Complex.I * ((1 - (m : ℤ) : ℤ) : ℂ))⁻¹) atTop (𝓝 0) := by
  refine tendsto_prim_of a ?_ (by omega)
  refine tendsto_atTop_mono (fun t => ?_) tendsto_abs_atTop_atTop
  have h := Complex.abs_im_le_norm ((a : ℂ) + (t : ℂ) * Complex.I)
  rwa [im_shift] at h

private lemma tendsto_prim_atBot (a : ℝ) (ha : a ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun t : ℝ => ((a : ℂ) + (t : ℂ) * Complex.I) ^ (1 - (m : ℤ)) *
        (Complex.I * ((1 - (m : ℤ) : ℤ) : ℂ))⁻¹) atBot (𝓝 0) := by
  refine tendsto_prim_of a ?_ (by omega)
  refine tendsto_atTop_mono (fun t => ?_) tendsto_abs_atBot_atTop
  have h := Complex.abs_im_le_norm ((a : ℂ) + (t : ℂ) * Complex.I)
  rwa [im_shift] at h

private lemma integral_shift_zpow_eq_zero (a : ℝ) (ha : a ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    ∫ t : ℝ, ((a : ℂ) + (t : ℂ) * Complex.I) ^ (-(m : ℤ)) = 0 := by
  have h := integral_of_hasDerivAt_of_tendsto (hasDerivAt_prim a ha hm)
    (integrable_shift_zpow a ha hm) (tendsto_prim_atBot a ha hm) (tendsto_prim_atTop a ha hm)
  simpa using h

private lemma shift_sub_eq (c p t : ℝ) :
    (c : ℂ) + (t : ℂ) * Complex.I - (p : ℂ) = ((c - p : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
  push_cast
  ring

private lemma one_div_pow_eq_zpow (z : ℂ) (m : ℕ) : 1 / z ^ m = z ^ (-(m : ℤ)) := by
  rw [one_div, zpow_neg, zpow_natCast]

private lemma integral_one_div_shift_eq_zero (a : ℝ) (ha : a ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    ∫ t : ℝ, 1 / (((a : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ m = 0 := by
  rw [show (fun t : ℝ => 1 / (((a : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ m) =
      (fun t : ℝ => (((a : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ (-(m : ℤ))) from by
    funext t
    exact one_div_pow_eq_zpow _ m]
  exact integral_shift_zpow_eq_zero a ha hm

theorem verticalIntegrable_one_div_pow {c p : ℝ} (hcp : c ≠ p)
    {m : ℕ} (hm : 2 ≤ m) :
    Complex.VerticalIntegrable
      (fun s : ℂ => 1 / (s - (p : ℂ)) ^ m) c volume := by
  have ha : c - p ≠ 0 := sub_ne_zero.mpr hcp
  have h := integrable_shift_zpow (c - p) ha hm
  refine h.congr ?_
  filter_upwards with t
  rw [one_div_pow_eq_zpow, shift_sub_eq]

theorem verticalIntegrable_const_mul_one_div_pow (z : ℂ)
    {c p : ℝ} (hcp : c ≠ p) {m : ℕ} (hm : 2 ≤ m) :
    Complex.VerticalIntegrable
      (fun s : ℂ => z * (1 / (s - (p : ℂ)) ^ m)) c volume :=
  (verticalIntegrable_one_div_pow hcp hm).const_mul z

theorem verticalIntegral_const_mul_one_div_pow_eq_zero (z : ℂ)
    {c p : ℝ} (hcp : c ≠ p) {m : ℕ} (hm : 2 ≤ m) :
    verticalIntegral c (fun s : ℂ => z * (1 / (s - (p : ℂ)) ^ m)) = 0 := by
  have ha : c - p ≠ 0 := sub_ne_zero.mpr hcp
  have h0 := integral_one_div_shift_eq_zero (c - p) ha hm
  simp only [verticalIntegral]
  rw [integral_const_mul]
  have hcongr : (fun t : ℝ => 1 / ((c : ℂ) + (t : ℂ) * Complex.I - (p : ℂ)) ^ m)
      =ᵐ[volume] (fun t : ℝ => 1 / (((c - p : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ m) := by
    filter_upwards with t
    rw [shift_sub_eq]
  rw [integral_congr_ae hcongr, h0, mul_zero, mul_zero]

end DedekindZetaZeroFree.LargeSieve.Vendor

end
