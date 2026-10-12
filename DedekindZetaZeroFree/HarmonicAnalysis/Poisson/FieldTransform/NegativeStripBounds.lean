module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.MeromorphicSpectrumExtension

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve

private lemma gamma_ne_zero_im {s : ℂ} (hs : s.im ≠ 0) :
    Complex.Gammaℂ s ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_
  · exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  · intro h0
    rw [Complex.Gamma_eq_zero_iff] at h0
    obtain ⟨m, hm⟩ := h0
    exact hs (by rw [hm]; simp)

private lemma gamma_ratio_shift (s : ℂ) (hs : s.im ≠ 0) :
    s.Gammaℂ / (1 - s).Gammaℂ =
      -((2 * Real.pi : ℂ) ^ 2 / s ^ 2) *
        ((s + 1).Gammaℂ / (-s).Gammaℂ) := by
  have hs0 : s ≠ 0 := by intro he; apply hs; rw [he]; simp
  have hms : -s ≠ 0 := neg_ne_zero.mpr hs0
  have hgam : s.Gammaℂ ≠ 0 := gamma_ne_zero_im hs
  have hgamm : (-s).Gammaℂ ≠ 0 := gamma_ne_zero_im (by simpa using neg_ne_zero.mpr hs)
  rw [Complex.Gammaℂ_add_one hs0]
  have heq : 1 - s = -s + 1 := by ring
  rw [heq, Complex.Gammaℂ_add_one hms]
  field_simp

private lemma shifted_gamma_bound (u v : ℝ) (r : ℕ) (hu : -1 < u) (huv : u ≤ v) :
    ∃ C : ℝ, ∃ m : ℕ, 0 < C ∧ ∀ s : ℂ,
      s.re ∈ Set.Icc u v → 1 ≤ |s.im| →
      ‖(s.Gammaℂ / (1 - s).Gammaℂ) ^ r‖ ≤ C * (1 + |s.im|) ^ m := by
  obtain ⟨C, m, hC, hbound⟩ := Vendor.gammaQuotient_polynomial_bound
    (show 0 < u + 1 by linarith) (show u + 1 ≤ v + 1 by linarith) r
  refine ⟨(2 * Real.pi) ^ (2 * r) * C, m, by positivity, ?_⟩
  intro s hs ht
  have hi : s.im ≠ 0 := by intro he; rw [he, abs_zero] at ht; norm_num at ht
  rw [gamma_ratio_shift s hi, mul_pow, norm_mul]
  have hf : ‖(-((2 * Real.pi : ℂ) ^ 2 / s ^ 2)) ^ r‖ ≤ (2 * Real.pi) ^ (2 * r) := by
    rw [norm_pow, norm_neg, norm_div, norm_pow, norm_pow]
    have hn : 1 ≤ ‖s‖ := ht.trans (Complex.abs_im_le_norm s)
    have hpi : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
      norm_cast
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hpi]
    calc ((2 * Real.pi) ^ 2 / ‖s‖ ^ 2) ^ r ≤ ((2 * Real.pi) ^ 2) ^ r := by
           gcongr
           exact div_le_self (by positivity) (one_le_pow₀ hn)
      _ = (2 * Real.pi) ^ (2 * r) := by rw [pow_mul]
  have he : 1 - (s + 1) = -s := by ring
  have hg := hbound (s + 1) (by simp; linarith [hs.1]) (by simp; linarith [hs.2])
  rw [he] at hg
  simpa only [Complex.add_im, Complex.one_im, add_zero, mul_assoc] using
    mul_le_mul hf hg (norm_nonneg _) (by positivity)

private lemma B_gamma_formula (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (s : ℂ)
    (hr : 1 ≤ r) (hs : s.im ≠ 0) :
    B D r h s = (D : ℂ) ^ (s - 1 / 2) *
      (s.Gammaℂ / (1 - s).Gammaℂ) ^ r *
        ((1 - s).Gammaℂ * Vendor.originMellinQ h (1 - s)) := by
  have hg : (1 - s).Gammaℂ ≠ 0 := gamma_ne_zero_im (by simpa using neg_ne_zero.mpr hs)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  simp only [B, Nat.add_sub_cancel, div_pow, pow_succ]
  simp only [Nat.succ_sub_one, inv_pow, div_pow]
  field_simp

private lemma D_strip_bound (D u v : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Set.Icc u v →
      ‖(D : ℂ) ^ (s - 1 / 2)‖ ≤ C := by
  have hc : ContinuousOn (fun σ : ℝ => D ^ (σ - 1 / 2)) (Set.Icc u v) :=
    (Real.continuous_const_rpow hD.ne').comp (by fun_prop) |>.continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro s hs
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]
  have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
  rw [hre]
  exact (le_abs_self _).trans ((hM s.re hs).trans (by simpa [Real.norm_eq_abs] using (le_abs_self M).trans (by linarith : |M| ≤ |M| + 1)))

theorem B_uniform_rapid_bound_negative_strip
    (D : ℝ) (r : ℕ) (b u v : ℝ) (k : ℕ)
    (hD : 0 < D) (hr : 1 ≤ r) (hb : 0 < b) (hu : -1 < u) (huv : u ≤ v) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
        (∀ x : ℝ, b < x → h x = 0) →
        ∀ σ : ℝ, σ ∈ Set.Icc u v → ∀ t : ℝ, 1 ≤ |t| →
          (1 + |t|) ^ k * ‖B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * Vendor.S b N h := by
  obtain ⟨Cγ, m, hCγ, hγ⟩ := shifted_gamma_bound u v r hu huv
  obtain ⟨CD, hCD, hDb⟩ := D_strip_bound D u v hD
  obtain ⟨N, CH, hCH, hH⟩ := Vendor.originMellin_source_vertical_bound b hb
    (1 - v) (1 - u) (by linarith) (k + m)
  refine ⟨N, CD * Cγ * CH, by positivity, ?_⟩
  intro h hh hc hp σ hσ t ht
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hre : s.re = σ := by simp [s]
  have him : s.im = t := by simp [s]
  have hi : s.im ≠ 0 := by rw [him]; intro he; rw [he, abs_zero] at ht; norm_num at ht
  have he : 1 - s = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    dsimp [s]; push_cast; ring
  have hbH := hH h hh hc hp (1 - σ) (-t) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    (by simpa using ht)
  rw [abs_neg, ← he] at hbH
  have hbγ := hγ s (by simpa [hre] using hσ) (by simpa [him] using ht)
  rw [him] at hbγ
  change (1 + |t|) ^ k * ‖B D r h s‖ ≤ _
  rw [B_gamma_formula D r h s hr hi, norm_mul, norm_mul]
  calc (1 + |t|) ^ k *
        (‖(D : ℂ) ^ (s - 1 / 2)‖ * ‖(s.Gammaℂ / (1 - s).Gammaℂ) ^ r‖ *
          ‖(1 - s).Gammaℂ * Vendor.originMellinQ h (1 - s)‖)
      ≤ (1 + |t|) ^ k * (CD * (Cγ * (1 + |t|) ^ m) *
          ‖(1 - s).Gammaℂ * Vendor.originMellinQ h (1 - s)‖) := by
        gcongr
        · exact hDb s (by simpa [hre] using hσ)
    _ = CD * Cγ * ((1 + |t|) ^ (k + m) *
          ‖(1 - s).Gammaℂ * Vendor.originMellinQ h (1 - s)‖) := by rw [pow_add]; ring
    _ ≤ CD * Cγ * (CH * Vendor.S b N h) := by gcongr
    _ = CD * Cγ * CH * Vendor.S b N h := by ring

private lemma S_mono (b : ℝ) (hb : 0 < b) (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) {n m : ℕ} (hnm : n ≤ m) :
    Vendor.S b n h ≤ Vendor.S b m h := by
  unfold Vendor.S
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
  intro i hi _
  have hi' := Finset.mem_range.mp hi
  exact le_trans (norm_nonneg _) (le_csSup
    (Vendor.S_finite b hb m h hh i (Finset.mem_range.mpr (by omega)))
    (Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr hb.le)))

private lemma gamma_continuous_pos {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt Complex.Gammaℂ s := by
  have hno : ∀ m : ℕ, s ≠ -m := by
    intro m he
    have : s.re = -(m : ℝ) := by rw [he]; simp
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have heq : Complex.Gammaℂ = fun z : ℂ =>
      2 * (2 * (Real.pi : ℂ)) ^ (-z) * Complex.Gamma z := by
    funext z; rw [Complex.Gammaℂ_def]
  rw [heq]
  have hb : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact (continuousAt_const.mul
    ((continuousAt_id.neg).const_cpow (Or.inl hb))).mul
      (Complex.differentiableAt_Gamma s hno).continuousAt

private lemma B_negative_low_bound (D : ℝ) (r : ℕ) (b δ : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hb : 0 < b) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
      Vendor.PositiveSideSupport b h → ∀ t : ℝ, |t| ≤ 1 →
      ‖B D r h ((-δ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Vendor.S b N h := by
  obtain ⟨N, CQ, hCQ, hQ⟩ := Vendor.originMellinQ_rectangle_source_bound
    b hb (1 + δ) (1 + δ)
  let s : ℝ → ℂ := fun t => (-δ : ℂ) + (t : ℂ) * Complex.I
  let F : ℝ → ℂ := fun t => (D : ℂ) ^ (s t - 1 / 2) *
      (((2 * Real.pi : ℝ) : ℂ) * Complex.Gammaℂ (s t + 1)) ^ r *
      ((Complex.Gammaℂ (1 - s t))⁻¹) ^ (r - 1) / (s t) ^ r
  have hsre (t : ℝ) : (s t + 1).re = 1 - δ := by simp [s]; ring
  have hsnz (t : ℝ) : s t ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp [s] at this
    linarith
  have hcont : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hsc : ContinuousAt s t := by fun_prop (disch := positivity)
    have hgamma : ContinuousAt (fun t => Complex.Gammaℂ (s t + 1)) t :=
      (gamma_continuous_pos (by rw [hsre]; linarith)).comp
        (hsc.add continuousAt_const)
    have hd : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    have hcp : ContinuousAt (fun t => (D : ℂ) ^ (s t - 1 / 2)) t :=
      (hsc.sub continuousAt_const).const_cpow (Or.inl hd)
    have hinv : ContinuousAt (fun t => (Complex.Gammaℂ (1 - s t))⁻¹) t :=
      Complex.differentiable_Gammaℂ_inv.continuous.continuousAt.comp
        (continuousAt_const.sub hsc)
    exact (((hcp.mul ((continuousAt_const.mul hgamma).pow r)).mul (hinv.pow (r - 1))).div
      (hsc.pow r) (pow_ne_zero _ (hsnz t)))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨N, max M 1 * CQ, mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hCQ, ?_⟩
  intro h hh hc hp t ht
  have hst : -1 < (s t).re := by simp [s]; linarith
  have hsQ : ‖Vendor.originMellinQ h (1 - s t)‖ ≤ CQ * Vendor.S b N h := by
    have he : 1 - s t = ((1 + δ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
      dsimp [s]; push_cast; ring
    apply hQ h hh hc hp (1 - s t) (by simp [s]) (by simp [s])
    simpa [he] using ht
  have hsB := B_eq_A_div D r h hD hr hh hc (s t) hst (hsnz t)
  change ‖B D r h (s t)‖ ≤ _
  rw [hsB]
  have heq : A D r h (s t) / (s t) ^ r = F t * Vendor.originMellinQ h (1 - s t) := by
    simp only [A, F]; ring
  rw [heq, norm_mul]
  calc ‖F t‖ * ‖Vendor.originMellinQ h (1 - s t)‖
      ≤ max M 1 * (CQ * Vendor.S b N h) := by
        gcongr
        exact (hM t (by simpa [abs_le] using ht)).trans (le_max_left _ _)
    _ = max M 1 * CQ * Vendor.S b N h := by ring

theorem B_negative_line_uniform_integral_bound
    (D : ℝ) (r : ℕ) (b δ : ℝ) (j : ℕ)
    (hD : 0 < D) (hr : 1 ≤ r) (hb : 0 < b)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
        (∀ x : ℝ, b < x → h x = 0) →
        Integrable (fun t : ℝ =>
          (-((-δ : ℂ) + (t : ℂ) * Complex.I)) ^ j *
            B D r h ((-δ : ℂ) + (t : ℂ) * Complex.I)) volume ∧
        (∫ t : ℝ, ‖(-((-δ : ℂ) + (t : ℂ) * Complex.I)) ^ j *
          B D r h ((-δ : ℂ) + (t : ℂ) * Complex.I)‖) ≤
            C * Vendor.S b N h := by
  obtain ⟨NH, CH, hCH, hH⟩ := B_uniform_rapid_bound_negative_strip D r b (-δ) (-δ)
    (j + 2) hD hr hb (by linarith) le_rfl
  obtain ⟨NL, CL, hCL, hL⟩ := B_negative_low_bound D r b δ hD hr hb hδ hδ1
  let N := max NH NL
  let C₀ := (1 + δ) ^ j * (CH + 2 ^ (j + 2) * CL)
  let w : ℝ → ℝ := fun t => (1 + |t|) ^ (-2 : ℝ)
  have hw : Integrable w volume := by
    simpa [w, Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp))
  have hw0 : ∀ t, 0 ≤ w t := by intro t; dsimp [w]; positivity
  let J := ∫ t, w t
  have hJ : 0 ≤ J := integral_nonneg hw0
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨N, C₀ * (J + 1), by positivity, ?_⟩
  intro h hh hc hp
  let s : ℝ → ℂ := fun t => (-δ : ℂ) + (t : ℂ) * Complex.I
  let f : ℝ → ℂ := fun t => (-(s t)) ^ j * B D r h (s t)
  have hS : 0 ≤ Vendor.S b N h := Vendor.S_nonneg b hb N h hh
  have hsnz (t : ℝ) : s t ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp [s] at this
    linarith
  have hsre (t : ℝ) : -1 < (s t).re := by simp [s]; linarith
  have hnorm (t : ℝ) : ‖s t‖ ≤ (1 + δ) * (1 + |t|) := by
    calc ‖s t‖ ≤ ‖(-δ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = δ + |t| := by simp [norm_mul, abs_of_pos hδ]
      _ ≤ (1 + δ) * (1 + |t|) := by nlinarith [abs_nonneg t]
  have hweighted (t : ℝ) : (1 + |t|) ^ 2 * ‖f t‖ ≤ C₀ * Vendor.S b N h := by
    have ht0 : 0 ≤ 1 + |t| := by positivity
    have hm : (1 + |t|) ^ 2 * ‖f t‖ ≤
        (1 + δ) ^ j * ((1 + |t|) ^ (j + 2) * ‖B D r h (s t)‖) := by
      dsimp [f]
      rw [norm_mul, norm_pow, norm_neg]
      calc (1 + |t|) ^ 2 * (‖s t‖ ^ j * ‖B D r h (s t)‖)
          ≤ (1 + |t|) ^ 2 * (((1 + δ) * (1 + |t|)) ^ j * ‖B D r h (s t)‖) := by
            gcongr; exact hnorm t
        _ = (1 + δ) ^ j * ((1 + |t|) ^ (j + 2) * ‖B D r h (s t)‖) := by
            rw [mul_pow, pow_add]; ring
    apply hm.trans
    by_cases ht : 1 ≤ |t|
    · have hbound := hH h hh hc hp (-δ) (by simp) t ht
      have hSm := S_mono b hb h hh (le_max_left NH NL)
      have hbound' : (1 + |t|) ^ (j + 2) * ‖B D r h (s t)‖ ≤ CH * Vendor.S b N h :=
        by simpa [s, N] using hbound.trans (mul_le_mul_of_nonneg_left hSm hCH.le)
      calc (1 + δ) ^ j * ((1 + |t|) ^ (j + 2) * ‖B D r h (s t)‖)
          ≤ (1 + δ) ^ j * (CH * Vendor.S b N h) := by gcongr
        _ ≤ C₀ * Vendor.S b N h := by dsimp [C₀]; nlinarith [show 0 ≤ (1 + δ) ^ j * (2 ^ (j + 2) * CL) by positivity]
    · have htl : |t| ≤ 1 := le_of_lt (lt_of_not_ge ht)
      have hbound := hL h hh hc hp t htl
      have hSm := S_mono b hb h hh (le_max_right NH NL)
      have hbound' : ‖B D r h (s t)‖ ≤ CL * Vendor.S b N h :=
        hbound.trans (mul_le_mul_of_nonneg_left hSm hCL.le)
      have ht2 : (1 + |t|) ^ (j + 2) ≤ (2 : ℝ) ^ (j + 2) := by gcongr; linarith
      calc (1 + δ) ^ j * ((1 + |t|) ^ (j + 2) * ‖B D r h (s t)‖)
          ≤ (1 + δ) ^ j * (2 ^ (j + 2) * (CL * Vendor.S b N h)) := by gcongr
        _ ≤ C₀ * Vendor.S b N h := by dsimp [C₀]; nlinarith [show 0 ≤ (1 + δ) ^ j * CH by positivity]
  have hdom (t : ℝ) : ‖f t‖ ≤ (C₀ * Vendor.S b N h) * w t := by
    have ht : 0 < (1 + |t|) ^ 2 := by positivity
    have he : w t = ((1 + |t|) ^ 2)⁻¹ := by
      dsimp [w]; rw [Real.rpow_neg (by positivity), Real.rpow_two]
    rw [he, ← div_eq_mul_inv, le_div_iff₀ ht, mul_comm]
    exact hweighted t
  have hcontB : Continuous (fun t => B D r h (s t)) := by
    have hA : Continuous (fun t => A D r h (s t)) :=
      (A_analyticOnNhd D r h hD hr hh hc).continuousOn.comp_continuous
        (by fun_prop) (fun t => hsre t)
    have he : (fun t => B D r h (s t)) = fun t => A D r h (s t) / (s t) ^ r := by
      funext t; exact B_eq_A_div D r h hD hr hh hc (s t) (hsre t) (hsnz t)
    rw [he]
    exact hA.div (by fun_prop) (fun t => pow_ne_zero _ (hsnz t))
  have hf : Integrable f volume :=
    (hw.const_mul (C₀ * Vendor.S b N h)).mono'
      ((by fun_prop : Continuous f).aestronglyMeasurable) (Filter.Eventually.of_forall hdom)
  refine ⟨hf, ?_⟩
  change (∫ t, ‖f t‖) ≤ _
  calc (∫ t, ‖f t‖) ≤ ∫ t, (C₀ * Vendor.S b N h) * w t :=
        integral_mono hf.norm (hw.const_mul _) hdom
    _ = C₀ * Vendor.S b N h * J := by rw [integral_const_mul]
    _ ≤ C₀ * (J + 1) * Vendor.S b N h := by nlinarith

end DedekindZetaZeroFree.LargeSieve

end
