module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.InverseMellinRepresentation

@[expose] public section

noncomputable section
open scoped Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve

theorem B_euler_inverse_integrable (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (j : ℕ) (c x : ℝ)
    (hc : 0 < c) (hx : 0 < x) :
    MeasureTheory.Integrable (fun t : ℝ =>
      (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)) *
        (-((c : ℂ) + (t : ℂ) * Complex.I)) ^ j *
          B D r h ((c : ℂ) + (t : ℂ) * Complex.I))
      MeasureTheory.volume := by
  obtain ⟨C, hCpos, hC⟩ := B_rapid_bound D r h c c (j + 3) hD hr hh hhc hc le_rfl
  have h1 : MeasureTheory.Integrable (fun t : ℝ => (1 + |t|) ^ (-((3 : ℕ) : ℝ)))
      MeasureTheory.volume := by
    simpa using (integrable_one_add_norm (E := ℝ) (r := 3) (by simp) :
      MeasureTheory.Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ))) MeasureTheory.volume)
  have h2 : MeasureTheory.Integrable (fun t : ℝ =>
      (x ^ (-c) * (1 + |c|) ^ j * C) * (1 + |t|) ^ (-((3 : ℕ) : ℝ))) MeasureTheory.volume :=
    h1.const_mul _
  refine h2.mono' ?_ ?_
  · have hexp : Continuous (fun t : ℝ => -((c : ℂ) + (t : ℂ) * Complex.I)) := by fun_prop
    have hBc : Continuous (fun t : ℝ => B D r h ((c : ℂ) + (t : ℂ) * Complex.I)) :=
      (B_differentiableOn D r h hD hr hh hhc).continuousOn.comp_continuous (by fun_prop) (by
        intro t
        show 0 < ((c : ℂ) + (t : ℂ) * Complex.I).re
        simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, hc])
    exact (((hexp.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).mul
      (hexp.pow j)).mul hBc).aestronglyMeasurable
  · filter_upwards with t
    set s : ℂ := (c : ℂ) + (t : ℂ) * Complex.I with hs
    have hs_bound : ‖s‖ ≤ (1 + |c|) * (1 + |t|) := by
      rw [hs]
      calc ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(c : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ :=
            norm_add_le _ _
        _ = |c| + |t| := by simp
        _ ≤ (1 + |c|) * (1 + |t|) := by
            nlinarith [abs_nonneg c, abs_nonneg t, mul_nonneg (abs_nonneg c) (abs_nonneg t)]
    have hx_bound : ‖(x : ℂ) ^ (-s)‖ = x ^ (-c) := by
      rw [hs, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im]
    have hb_bound : ‖(-s) ^ j‖ ≤ ((1 + |c|) * (1 + |t|)) ^ j := by
      rw [norm_pow, norm_neg]
      exact pow_le_pow_left₀ (norm_nonneg _) hs_bound j
    have hB_bound : ‖B D r h s‖ ≤ C * (1 + |t|) ^ (-((j + 3 : ℕ) : ℝ)) := by
      have ha : 0 < (1 + |t|) ^ (j + 3) := by positivity
      have hh' := hC c (by simp [hc.le]) t
      have hpow : (1 + |t|) ^ (-((j + 3 : ℕ) : ℝ)) = ((1 + |t|) ^ (j + 3))⁻¹ := by
        rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |t|), Real.rpow_natCast]
      rw [hpow, ← div_eq_mul_inv, le_div_iff₀ ha]
      simpa [hs, mul_comm] using hh'
    have key : (1 + |t|) ^ j * (1 + |t|) ^ (-((j + 3 : ℕ) : ℝ)) =
        (1 + |t|) ^ (-((3 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast (1 + |t|) j, ← Real.rpow_add (by positivity : 0 < 1 + |t|)]
      congr 1
      push_cast
      ring
    calc ‖(x : ℂ) ^ (-s) * (-s) ^ j * B D r h s‖
        = ‖(x : ℂ) ^ (-s)‖ * ‖(-s) ^ j‖ * ‖B D r h s‖ := by rw [norm_mul, norm_mul]
      _ = x ^ (-c) * ‖(-s) ^ j‖ * ‖B D r h s‖ := by rw [hx_bound]
      _ ≤ x ^ (-c) * ((1 + |c|) * (1 + |t|)) ^ j *
            (C * (1 + |t|) ^ (-((j + 3 : ℕ) : ℝ))) := by
          have hxnn : 0 ≤ x ^ (-c) := Real.rpow_nonneg hx.le _
          calc x ^ (-c) * ‖(-s) ^ j‖ * ‖B D r h s‖
              ≤ x ^ (-c) * ((1 + |c|) * (1 + |t|)) ^ j * ‖B D r h s‖ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb_bound hxnn) (norm_nonneg _)
            _ ≤ x ^ (-c) * ((1 + |c|) * (1 + |t|)) ^ j *
                  (C * (1 + |t|) ^ (-((j + 3 : ℕ) : ℝ))) :=
                mul_le_mul_of_nonneg_left hB_bound (by positivity)
      _ = x ^ (-c) * (1 + |c|) ^ j * C *
            ((1 + |t|) ^ j * (1 + |t|) ^ (-((j + 3 : ℕ) : ℝ))) := by
          rw [mul_pow]; ring
      _ = (x ^ (-c) * (1 + |c|) ^ j * C) * (1 + |t|) ^ (-((3 : ℕ) : ℝ)) := by rw [key]

open MeasureTheory Filter

def line (c t : ℝ) : ℂ := (c : ℂ) + (t : ℂ) * Complex.I
def integrand (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (j : ℕ) (c x t : ℝ) : ℂ :=
  (x : ℂ) ^ (-line c t) * (-line c t) ^ j * B D r h (line c t)

private lemma integrand_integrable (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h)
    (j : ℕ) (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    Integrable (integrand D r h j c x) :=
  B_euler_inverse_integrable D r h hD hr hh hhc j c x hc hx

private lemma integrand_norm (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (j : ℕ) (c x t : ℝ) (hx : 0 < x) :
    ‖integrand D r h j c x t‖ =
      x ^ (-c) * ‖(-line c t) ^ j * B D r h (line c t)‖ := by
  unfold integrand
  rw [mul_assoc, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [line, Complex.mul_re]

private lemma weighted_integrable (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h)
    (j : ℕ) (c : ℝ) (hc : 0 < c) :
    Integrable (fun t => (-line c t) ^ j * B D r h (line c t)) := by
  convert integrand_integrable D r h hD hr hh hhc j c 1 hc (by norm_num) using 1
  funext t
  simp [integrand]

private lemma integrand_deriv (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (j : ℕ) (c x t : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y => integrand D r h j c y t)
      ((x : ℂ)⁻¹ * integrand D r h (j + 1) c x t) x := by
  have hd := (Complex.hasStrictDerivAt_cpow_const (c := -line c t)
    (Complex.ofReal_mem_slitPlane.mpr hx)).hasDerivAt.comp_ofReal
  convert (hd.mul_const ((-line c t) ^ j)).mul_const (B D r h (line c t)) using 1
  · rfl
  · rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_one]
    simp only [integrand, pow_succ, div_eq_mul_inv]
    ring

private lemma inverse_deriv (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h)
    (j : ℕ) (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    HasDerivAt (mellinInv c (fun s => (-s) ^ j * B D r h s))
      ((x : ℂ)⁻¹ * mellinInv c (fun s => (-s) ^ (j + 1) * B D r h s) x) x := by
  have hweight := weighted_integrable D r h hD hr hh hhc (j + 1) c hc
  have hbound : Integrable (fun t => (x / 2) ^ (-c - 1) *
      ‖(-line c t) ^ (j + 1) * B D r h (line c t)‖) := hweight.norm.const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y => integrand D r h j c y)
    (F' := fun y t => (y : ℂ)⁻¹ * integrand D r h (j + 1) c y t)
    (s := Set.Ioi (x / 2)) (bound := fun t => (x / 2) ^ (-c - 1) *
      ‖(-line c t) ^ (j + 1) * B D r h (line c t)‖)
    (Ioi_mem_nhds (by linarith : x / 2 < x))
    (eventually_of_mem (Ioi_mem_nhds hx) (fun y hy =>
      (integrand_integrable D r h hD hr hh hhc j c y hc hy).aestronglyMeasurable))
    (integrand_integrable D r h hD hr hh hhc j c x hc hx)
    ((integrand_integrable D r h hD hr hh hhc (j + 1) c x hc hx).const_mul _).aestronglyMeasurable
    (Eventually.of_forall (fun t y hy => by
      have hypos : 0 < y := lt_trans (by positivity : 0 < x / 2) hy
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos,
        integrand_norm D r h (j + 1) c y t hypos]
      have heq : y⁻¹ * y ^ (-c) = y ^ (-c - 1) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hypos]
        congr 1
        ring
      rw [← mul_assoc, heq]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos (by positivity : 0 < x / 2) hy.le (by linarith))
        (norm_nonneg _))) hbound
    (Eventually.of_forall (fun t y hy => integrand_deriv D r h j c y t
      (lt_trans (by positivity : 0 < x / 2) hy)))
  have hkey := key.2.const_mul (((1 / (2 * Real.pi)) : ℝ) : ℂ)
  simp only [integral_const_mul] at hkey
  change HasDerivAt (fun y => mellinInv c (fun s => (-s) ^ j * B D r h s) y) _ x
  convert hkey using 1
  · funext y
    simp [mellinInv, integrand, line, RCLike.real_smul_eq_coe_mul, mul_assoc]
  · simp [mellinInv, integrand, line, RCLike.real_smul_eq_coe_mul, mul_assoc, mul_left_comm]

private lemma inverse_smooth (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h)
    (c : ℝ) (hc : 0 < c) :
    ∀ (k j : ℕ), ContDiffOn ℝ (k : ℕ∞ω)
      (mellinInv c (fun s => (-s) ^ j * B D r h s)) (Set.Ioi 0) := by
  have hd : ∀ j : ℕ, DifferentiableOn ℝ
      (mellinInv c (fun s => (-s) ^ j * B D r h s)) (Set.Ioi 0) :=
    fun j x hx => (inverse_deriv D r h hD hr hh hhc j c x hc hx).differentiableAt.differentiableWithinAt
  intro k
  induction k with
  | zero => intro j; exact contDiffOn_zero.mpr (hd j).continuousOn
  | succ k ih =>
    intro j
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨hd j, by simp, ?_⟩
    have hinv : ContDiffOn ℝ (k : ℕ∞ω) (fun x : ℝ => (x : ℂ)⁻¹) (Set.Ioi 0) := by
      apply ContDiffOn.inv Complex.ofRealCLM.contDiff.contDiffOn
      intro x hx
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
    exact (hinv.mul (ih (j + 1))).congr fun x hx =>
      (inverse_deriv D r h hD hr hh hhc j c x hc hx).deriv

theorem fieldTransform_contDiffOn (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) :
    ContDiffOn ℝ ∞ (fieldTransform D r h) (Set.Ioi 0) := by
  have hs : ContDiffOn ℝ ∞ (mellinInv 2 (B D r h)) (Set.Ioi 0) := by
    apply contDiffOn_infty.mpr
    intro k
    simpa using inverse_smooth D r h hD hr hh hhc 2 (by norm_num) k 0
  exact hs.congr fun x hx => by simp [fieldTransform, Set.mem_Ioi.mp hx]

theorem EulerIter_fieldTransform_eq_mellinInv
    (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (j : ℕ) (c x : ℝ)
    (hc : 0 < c) (hx : 0 < x) :
    Vendor.EulerIter j (fieldTransform D r h) x =
      mellinInv c (fun s : ℂ => (-s) ^ j * B D r h s) x := by
  induction j generalizing x with
  | zero =>
    simpa [fieldTransform, hx] using (B_mellinInv_eq D r h hD hr hh hhc c x hc hx).symm
  | succ j ih =>
    rw [Vendor.EulerIter_succ_of_pos j _ x hx]
    have heq : Vendor.EulerIter j (fieldTransform D r h) =ᶠ[nhds x]
        mellinInv c (fun s => (-s) ^ j * B D r h s) :=
      eventually_of_mem (Ioi_mem_nhds hx) (fun y hy => ih y hy)
    rw [heq.deriv_eq, (inverse_deriv D r h hD hr hh hhc j c x hc hx).deriv]
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hx.ne'), one_mul]

private lemma inverse_bound (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h)
    (j : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖mellinInv c (fun s => (-s) ^ j * B D r h s) x‖ ≤ C * x ^ (-c) := by
  let A : ℝ := ∫ t : ℝ, ‖(-line c t) ^ j * B D r h (line c t)‖
  refine ⟨|1 / (2 * Real.pi)| * A, mul_nonneg (abs_nonneg _) (integral_nonneg (fun t => norm_nonneg _)), ?_⟩
  intro x hx
  have hi : (∫ t : ℝ, ‖integrand D r h j c x t‖) = x ^ (-c) * A := by
    simp_rw [integrand_norm D r h j c x _ hx]
    exact integral_const_mul _ _
  have heq : mellinInv c (fun s => (-s) ^ j * B D r h s) x =
      (1 / (2 * Real.pi)) • ∫ t : ℝ, integrand D r h j c x t := by
    simp [mellinInv, integrand, line, mul_assoc, smul_eq_mul]
  rw [heq, norm_smul, Real.norm_eq_abs]
  calc |1 / (2 * Real.pi)| * ‖∫ t : ℝ, integrand D r h j c x t‖
      ≤ |1 / (2 * Real.pi)| * ∫ t : ℝ, ‖integrand D r h j c x t‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (abs_nonneg _)
    _ = (|1 / (2 * Real.pi)| * A) * x ^ (-c) := by rw [hi]; ring

theorem fieldTransform_euler_two_ended_bound
    (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (j n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ x : ℝ, 0 < x → x ≤ 1 →
        ‖Vendor.EulerIter j (fieldTransform D r h) x‖ ≤ C * Real.rpow x (-δ)) ∧
      (∀ x : ℝ, 1 ≤ x →
        ‖Vendor.EulerIter j (fieldTransform D r h) x‖ ≤
          C * Real.rpow x (-(n : ℝ))) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := inverse_bound D r h hD hr hh hhc j δ hδ
  obtain ⟨C₂, hC₂, hb₂⟩ := inverse_bound D r h hD hr hh hhc j (n + 1) (by positivity)
  refine ⟨C₁ + C₂ + 1, by linarith, ?_, ?_⟩
  · intro x hx _
    rw [EulerIter_fieldTransform_eq_mellinInv D r h hD hr hh hhc j δ x hδ hx]
    exact (hb₁ x hx).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hx.le _))
  · intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    rw [EulerIter_fieldTransform_eq_mellinInv D r h hD hr hh hhc j (n + 1) x (by positivity) hxpos]
    calc ‖mellinInv (n + 1) (fun s => (-s) ^ j * B D r h s) x‖
        ≤ C₂ * x ^ (-(n + 1 : ℝ)) := hb₂ x hxpos
      _ ≤ C₂ * x ^ (-(n : ℝ)) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) hC₂
      _ ≤ (C₁ + C₂ + 1) * x ^ (-(n : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hxpos.le _)

end DedekindZetaZeroFree.LargeSieve

end
