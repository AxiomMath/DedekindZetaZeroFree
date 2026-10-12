module

public import DedekindZetaZeroFree.Analysis.MellinVerticalIntegral

@[expose] public section

noncomputable section
open MeasureTheory Filter Complex
open scoped Real Topology

namespace DedekindZetaZeroFree.LargeSieve.Vendor

private lemma norm_add_mul_I_sq (a t : ℝ) :
    ‖((a : ℂ) + (t : ℂ) * I)‖ ^ 2 = a ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]

private lemma one_add_mul_I_ne_zero (t : ℝ) : (1 : ℂ) + (t : ℂ) * I ≠ 0 := by
  intro h
  have h1 : ((1 : ℂ) + (t : ℂ) * I).re = 1 := by simp
  rw [h] at h1
  simp at h1

private lemma integrable_one_div_one_add_mul_I_pow {k : ℕ} (hk : 2 ≤ k) :
    Integrable (fun t : ℝ => (1 : ℂ) / ((1 : ℂ) + (t : ℂ) * I) ^ k) volume := by
  refine Integrable.mono' integrable_inv_one_add_sq ?_ ?_
  · exact (continuous_const.div (by fun_prop) (fun t => pow_ne_zero k (one_add_mul_I_ne_zero t))
      ).aestronglyMeasurable
  · filter_upwards with t
    have hsq : ‖((1 : ℂ) + (t : ℂ) * I)‖ ^ 2 = 1 + t ^ 2 := by
      have h := norm_add_mul_I_sq 1 t
      simpa using h
    have hge : 1 ≤ ‖((1 : ℂ) + (t : ℂ) * I)‖ := by
      have h1 : 1 ≤ ‖((1 : ℂ) + (t : ℂ) * I)‖ ^ 2 := by rw [hsq]; linarith [sq_nonneg t]
      nlinarith [norm_nonneg ((1 : ℂ) + (t : ℂ) * I)]
    have hpow : 1 + t ^ 2 ≤ ‖((1 : ℂ) + (t : ℂ) * I)‖ ^ k := by
      calc 1 + t ^ 2 = ‖((1 : ℂ) + (t : ℂ) * I)‖ ^ 2 := hsq.symm
        _ ≤ ‖((1 : ℂ) + (t : ℂ) * I)‖ ^ k := pow_le_pow_right₀ hge hk
    rw [norm_div, norm_one, norm_pow, one_div]
    exact inv_anti₀ (by positivity) hpow

private lemma integrable_one_div_add_mul_I_pow {a : ℝ} (ha : a ≠ 0) {k : ℕ} (hk : 2 ≤ k) :
    Integrable (fun t : ℝ => (1 : ℂ) / ((a : ℂ) + (t : ℂ) * I) ^ k) volume := by
  have h1 := integrable_one_div_one_add_mul_I_pow (k := k) hk
  have h2 : Integrable (fun t : ℝ => (1 : ℂ) / ((1 : ℂ) + ((a⁻¹ * t : ℝ) : ℂ) * I) ^ k)
      volume := h1.comp_mul_left' (inv_ne_zero ha)
  have h3 : Integrable
      (fun t : ℝ => ((a : ℂ) ^ k)⁻¹ * ((1 : ℂ) / ((1 : ℂ) + ((a⁻¹ * t : ℝ) : ℂ) * I) ^ k))
      volume := h2.const_mul _
  refine h3.congr (Filter.Eventually.of_forall (fun t => ?_))
  simp only []
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hfac : (1 : ℂ) + ((a⁻¹ * t : ℝ) : ℂ) * I = (a : ℂ)⁻¹ * ((a : ℂ) + (t : ℂ) * I) := by
    have h : ((a⁻¹ * t : ℝ) : ℂ) = (a : ℂ)⁻¹ * (t : ℂ) := by push_cast; ring
    rw [h, mul_add, mul_assoc, inv_mul_cancel₀ hac]
  rw [one_div, one_div, hfac, mul_pow, mul_inv, ← mul_assoc, ← mul_inv, ← mul_pow,
    mul_inv_cancel₀ hac, one_pow, inv_one, one_mul]

private lemma abs_le_norm_add_mul_I (a t : ℝ) : |t| ≤ ‖((a : ℂ) + (t : ℂ) * I)‖ := by
  have h : |t| ^ 2 ≤ ‖((a : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    rw [norm_add_mul_I_sq, sq_abs]; linarith [sq_nonneg a]
  nlinarith [abs_nonneg t, norm_nonneg ((a : ℂ) + (t : ℂ) * I)]

private lemma tendsto_norm_add_mul_I_atTop (a : ℝ) :
    Tendsto (fun t : ℝ => ‖((a : ℂ) + (t : ℂ) * I)‖) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨max b 0, fun t ht => ?_⟩
  have h1 : b ≤ t := le_trans (le_max_left b 0) ht
  have h2 : 0 ≤ t := le_trans (le_max_right b 0) ht
  have hb : b ≤ |t| := by rw [abs_of_nonneg h2]; exact h1
  exact le_trans hb (abs_le_norm_add_mul_I a t)

private lemma tendsto_norm_add_mul_I_atBot (a : ℝ) :
    Tendsto (fun t : ℝ => ‖((a : ℂ) + (t : ℂ) * I)‖) atBot atTop := by
  rw [tendsto_atBot_atTop]
  intro b
  refine ⟨min (-b) 0, fun t ht => ?_⟩
  have h1 : t ≤ -b := le_trans ht (min_le_left _ _)
  have h2 : t ≤ 0 := le_trans ht (min_le_right _ _)
  have hb : b ≤ |t| := by rw [abs_of_nonpos h2]; linarith
  exact le_trans hb (abs_le_norm_add_mul_I a t)

theorem verticalIntegrable_higher_principal_part (R : ℂ)
    {p c : ℝ} (hcp : c ≠ p) {k : ℕ} (hk : 2 ≤ k) :
    Complex.VerticalIntegrable
      (fun s : ℂ => R / (s - (p : ℂ)) ^ k) c volume := by
  have ha : c - p ≠ 0 := sub_ne_zero.mpr hcp
  have hbase := integrable_one_div_add_mul_I_pow (a := c - p) ha hk
  have hR : Integrable (fun t : ℝ => R / (((c - p : ℝ) : ℂ) + (t : ℂ) * I) ^ k) volume :=
    (hbase.const_mul R).congr (Filter.Eventually.of_forall (fun t => by
      simp only []
      rw [one_div, div_eq_mul_inv]))
  show Integrable (fun t : ℝ => R / (((c : ℂ) + (t : ℂ) * I) - (p : ℂ)) ^ k) volume
  refine hR.congr (Filter.Eventually.of_forall (fun t => ?_))
  have hpt : ((c : ℂ) + (t : ℂ) * I) - (p : ℂ) = (((c - p : ℝ) : ℂ) + (t : ℂ) * I) := by
    push_cast; ring
  simp only []
  rw [← hpt]

theorem verticalIntegral_higher_principal_part_eq_zero (R : ℂ)
    {p c : ℝ} (hcp : c ≠ p) {k : ℕ} (hk : 2 ≤ k) :
    verticalIntegral c (fun s : ℂ => R / (s - (p : ℂ)) ^ k) = 0 := by
  set a : ℝ := c - p with ha_def
  have ha : a ≠ 0 := by rw [ha_def]; exact sub_ne_zero.mpr hcp
  have hbase := integrable_one_div_add_mul_I_pow (a := a) ha hk
  have hint : Integrable (fun t : ℝ => R / ((a : ℂ) + (t : ℂ) * I) ^ k) volume :=
    (hbase.const_mul R).congr (Filter.Eventually.of_forall (fun t => by
      simp only []
      rw [one_div, div_eq_mul_inv]))
  set m : ℤ := 1 - (k : ℤ) with hm_def
  have hmneg : m < 0 := by rw [hm_def]; omega
  set c₀ : ℂ := -(R / (((((k : ℤ) - 1 : ℤ)) : ℂ) * I)) with hc₀_def
  have hk1 : ((k : ℤ) - 1) ≠ 0 := by omega
  have hX : ((((k : ℤ) - 1 : ℤ)) : ℂ) ≠ 0 := fun h => hk1 (by exact_mod_cast h)
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => c₀ * ((a : ℂ) + (t : ℂ) * I) ^ m)
      (R / ((a : ℂ) + (t : ℂ) * I) ^ k) t := by
    intro t
    have hu : HasDerivAt (fun t : ℝ => (a : ℂ) + (t : ℂ) * I) I t := by
      have h := (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I
      simpa using h.const_add (a : ℂ)
    have hune : (a : ℂ) + (t : ℂ) * I ≠ 0 := by
      intro h
      have h1 : ((a : ℂ) + (t : ℂ) * I).re = a := by simp
      rw [h] at h1
      simp at h1
      exact ha h1.symm
    have hcomp := HasDerivAt.comp t (hasDerivAt_zpow m ((a : ℂ) + (t : ℂ) * I) (Or.inl hune)) hu
    have hmain : HasDerivAt (fun t : ℝ => c₀ * ((a : ℂ) + (t : ℂ) * I) ^ m)
        (c₀ * (((m : ℂ) * ((a : ℂ) + (t : ℂ) * I) ^ (m - 1)) * I)) t := by
      simpa only [Function.comp_def] using hcomp.const_mul c₀
    have hval : c₀ * (((m : ℂ) * ((a : ℂ) + (t : ℂ) * I) ^ (m - 1)) * I) =
        R / ((a : ℂ) + (t : ℂ) * I) ^ k := by
      have hm1 : m - 1 = -(k : ℤ) := by rw [hm_def]; ring
      have hpow : ((a : ℂ) + (t : ℂ) * I) ^ (m - 1) = (((a : ℂ) + (t : ℂ) * I) ^ k)⁻¹ := by
        rw [hm1, zpow_neg, zpow_natCast]
      have hA : (m : ℂ) = -((((k : ℤ) - 1 : ℤ)) : ℂ) := by rw [hm_def]; push_cast; ring
      have hcoef : c₀ * ((m : ℂ) * I) = R := by
        rw [hA, hc₀_def]
        have hXI : ((((k : ℤ) - 1 : ℤ)) : ℂ) * I ≠ 0 := mul_ne_zero hX Complex.I_ne_zero
        field_simp
      have hstep : c₀ * (((m : ℂ) * ((a : ℂ) + (t : ℂ) * I) ^ (m - 1)) * I)
          = (c₀ * ((m : ℂ) * I)) * ((a : ℂ) + (t : ℂ) * I) ^ (m - 1) := by ring
      rw [hstep, hcoef, hpow, div_eq_mul_inv]
    rwa [hval] at hmain
  have hlimTop : Tendsto (fun t : ℝ => c₀ * ((a : ℂ) + (t : ℂ) * I) ^ m) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => ((a : ℂ) + (t : ℂ) * I) ^ m) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine Tendsto.congr' ?_
        ((tendsto_zpow_atTop_zero (𝕜 := ℝ) hmneg).comp (tendsto_norm_add_mul_I_atTop a))
      filter_upwards with t
      exact (Complex.norm_zpow _ m).symm
    simpa using h1.const_mul c₀
  have hlimBot : Tendsto (fun t : ℝ => c₀ * ((a : ℂ) + (t : ℂ) * I) ^ m) atBot (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => ((a : ℂ) + (t : ℂ) * I) ^ m) atBot (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine Tendsto.congr' ?_
        ((tendsto_zpow_atTop_zero (𝕜 := ℝ) hmneg).comp (tendsto_norm_add_mul_I_atBot a))
      filter_upwards with t
      exact (Complex.norm_zpow _ m).symm
    simpa using h1.const_mul c₀
  have hzero : ∫ t : ℝ, R / ((a : ℂ) + (t : ℂ) * I) ^ k = 0 := by
    have h := integral_of_hasDerivAt_of_tendsto hderiv hint hlimBot hlimTop
    simpa using h
  have hpt : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * I) - (p : ℂ) = (a : ℂ) + (t : ℂ) * I := by
    intro t; rw [ha_def]; push_cast; ring
  rw [verticalIntegral]
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun t => by
    show R / (((c : ℂ) + (t : ℂ) * I) - (p : ℂ)) ^ k = R / ((a : ℂ) + (t : ℂ) * I) ^ k
    rw [hpt t])), hzero, mul_zero]

theorem norm_higher_principal_part_le_on_strip (R : ℂ) (p : ℝ)
    {k : ℕ} (hk : 2 ≤ k) {a b : ℝ} {s : ℂ}
    (hs : s.re ∈ Set.Icc a b) (him : 1 ≤ |s.im|) :
    ‖R / (s - (p : ℂ)) ^ k‖ ≤ ‖R‖ := by
  have hre : (s - (p : ℂ)).re = s.re - p := by simp
  have him' : (s - (p : ℂ)).im = s.im := by simp
  have hsq : ‖s - (p : ℂ)‖ ^ 2 = (s.re - p) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him']
    ring
  have hge : 1 ≤ ‖s - (p : ℂ)‖ := by
    have h1 : 1 ≤ ‖s - (p : ℂ)‖ ^ 2 := by
      rw [hsq]
      nlinarith [him, abs_nonneg s.im, sq_abs s.im, sq_nonneg (s.re - p)]
    nlinarith [norm_nonneg (s - (p : ℂ))]
  have hpos : 0 < ‖s - (p : ℂ)‖ ^ k := pow_pos (by linarith) k
  rw [norm_div, norm_pow, div_le_iff₀ hpos]
  exact le_mul_of_one_le_right (norm_nonneg R) (one_le_pow₀ hge)

end DedekindZetaZeroFree.LargeSieve.Vendor

end
