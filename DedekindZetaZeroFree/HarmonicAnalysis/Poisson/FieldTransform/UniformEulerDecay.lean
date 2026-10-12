module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.EulerDerivativesAndDecay

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff
open MeasureTheory

namespace DedekindZetaZeroFree.LargeSieve

private lemma uniform_complex_norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

private lemma uniform_norm_add_mul_I_le (c t v : ℝ) (hc0 : 0 ≤ c) (hcv : c ≤ v) (hv0 : 0 ≤ v) :
    ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ≤ (v + 1) * (1 + |t|) := by
  calc ‖(c : ℂ) + (t : ℂ) * Complex.I‖
      ≤ ‖(c : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |c| + |t| := by
        rw [uniform_complex_norm_ofReal, norm_mul, uniform_complex_norm_ofReal,
          Complex.norm_I, mul_one]
    _ = c + |t| := by rw [abs_of_nonneg hc0]
    _ ≤ v + |t| := by linarith
    _ ≤ (v + 1) * (1 + |t|) := by nlinarith [abs_nonneg t, hv0]

private lemma uniform_abs_rpow_neg_two_le (t : ℝ) :
    (1 + |t|) ^ (-2 : ℝ) ≤ 2 * (1 + t ^ 2)⁻¹ := by
  rw [Real.rpow_neg (by positivity), Real.rpow_two, ← one_div, ← div_eq_mul_inv]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [abs_nonneg t, sq_abs t, sq_nonneg t]

private lemma uniform_integrable_one_add_abs_rpow_neg_two :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-2 : ℝ)) := by
  simpa using (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp))

private lemma uniform_integral_one_add_abs_rpow_neg_two_le :
    ∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ) ≤ 2 * Real.pi := by
  have h := integral_mono_of_nonneg (μ := volume)
    (Filter.Eventually.of_forall (fun t => Real.rpow_nonneg (by positivity) _))
    (integrable_inv_one_add_sq.const_mul 2)
    (Filter.Eventually.of_forall (fun t => uniform_abs_rpow_neg_two_le t))
  rwa [integral_const_mul, integral_univ_inv_one_add_sq] at h

private lemma uniform_rpow_pow_mul_inv (u : ℝ) (hu : 0 < u) (j : ℕ) :
    u ^ j * (u ^ (j + 2))⁻¹ = u ^ (-2 : ℝ) := by
  rw [← Real.rpow_natCast u j, ← Real.rpow_natCast u (j + 2), ← Real.rpow_neg hu.le,
    ← Real.rpow_add hu]
  push_cast
  ring_nf

private lemma uniform_jet_mul_bound (u : ℝ) (hu : 0 < u) (j : ℕ) (X Y : ℝ)
    (hXY : u ^ (j + 2) * Y ≤ X) :
    u ^ j * Y ≤ X * u ^ (-2 : ℝ) := by
  have hu2 : (0 : ℝ) < u ^ (j + 2) := by positivity
  have hY : Y ≤ X * (u ^ (j + 2))⁻¹ := by
    rw [le_mul_inv_iff₀ hu2, mul_comm]; exact hXY
  calc u ^ j * Y ≤ u ^ j * (X * (u ^ (j + 2))⁻¹) :=
        mul_le_mul_of_nonneg_left hY (by positivity)
    _ = X * (u ^ j * (u ^ (j + 2))⁻¹) := by ring
    _ = X * u ^ (-2 : ℝ) := by rw [uniform_rpow_pow_mul_inv u hu j]

private lemma uniform_norm_mellinInv_le (c x A : ℝ) (g : ℂ → ℂ) (hx : 0 < x) (hA : 0 ≤ A)
    (hint : Integrable (fun t : ℝ =>
      (x : ℂ) ^ (-(c + (t : ℂ) * Complex.I)) * g (c + (t : ℂ) * Complex.I)))
    (hbound : ∀ t : ℝ, ‖g (c + (t : ℂ) * Complex.I)‖ ≤ A * (1 + |t|) ^ (-2 : ℝ)) :
    ‖mellinInv c g x‖ ≤ A * x ^ (-c) := by
  set F : ℝ → ℂ := fun t => (x : ℂ) ^ (-(c + (t : ℂ) * Complex.I)) * g (c + (t : ℂ) * Complex.I)
    with hF
  have hFn : ∀ t, ‖F t‖ = x ^ (-c) * ‖g (c + (t : ℂ) * Complex.I)‖ := by
    intro t
    rw [hF, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    congr 1
    simp [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re]
  have hmaj_int : Integrable (fun t : ℝ => x ^ (-c) * A * (1 + |t|) ^ (-2 : ℝ)) := by
    have h := (uniform_integrable_one_add_abs_rpow_neg_two.const_mul (x ^ (-c) * A))
    simpa [mul_assoc] using h
  have hle : ∫ t, ‖F t‖ ≤ ∫ t, x ^ (-c) * A * (1 + |t|) ^ (-2 : ℝ) := by
    apply integral_mono hint.norm hmaj_int
    intro t
    change ‖F t‖ ≤ x ^ (-c) * A * (1 + |t|) ^ (-2 : ℝ)
    rw [hFn t]
    have hxc : 0 ≤ x ^ (-c) := Real.rpow_nonneg hx.le _
    calc x ^ (-c) * ‖g (c + (t : ℂ) * Complex.I)‖
        ≤ x ^ (-c) * (A * (1 + |t|) ^ (-2 : ℝ)) := mul_le_mul_of_nonneg_left (hbound t) hxc
      _ = x ^ (-c) * A * (1 + |t|) ^ (-2 : ℝ) := by ring
  have hIeq : ∫ t, x ^ (-c) * A * (1 + |t|) ^ (-2 : ℝ)
      = x ^ (-c) * A * ∫ t, (1 + |t|) ^ (-2 : ℝ) := by
    rw [← integral_const_mul]
  have hscal : ‖(1 / (2 * Real.pi) : ℝ)‖ = 1 / (2 * Real.pi) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hInv : mellinInv c g x = (1 / (2 * Real.pi)) • ∫ t, F t := by
    rw [mellinInv]
    congr 1
  rw [hInv, norm_smul, hscal]
  calc (1 / (2 * Real.pi)) * ‖∫ t, F t‖
      ≤ (1 / (2 * Real.pi)) * ∫ t, ‖F t‖ := by
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm F) (by positivity)
    _ ≤ (1 / (2 * Real.pi)) * (x ^ (-c) * A * ∫ t, (1 + |t|) ^ (-2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← hIeq]; exact hle
    _ ≤ (1 / (2 * Real.pi)) * (x ^ (-c) * A * (2 * Real.pi)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left uniform_integral_one_add_abs_rpow_neg_two_le
            (mul_nonneg (Real.rpow_nonneg hx.le _) hA)
        · positivity
    _ = A * x ^ (-c) := by field_simp

theorem fieldTransform_uniform_euler_two_ended_bound
    (D : ℝ) (r : ℕ) (b : ℝ) (j n : ℕ) (δ : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hb : 0 < b) (hδ : 0 < δ) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
        Vendor.PositiveSideSupport b h →
        (∀ x : ℝ, 0 < x → x ≤ 1 →
          ‖Vendor.EulerIter j (fieldTransform D r h) x‖ ≤
            C * Vendor.S b N h * Real.rpow x (-δ)) ∧
        (∀ x : ℝ, 1 ≤ x →
          ‖Vendor.EulerIter j (fieldTransform D r h) x‖ ≤
            C * Vendor.S b N h * Real.rpow x (-(n : ℝ))) := by
  set a : ℝ := min δ ((n : ℝ) + 1) with ha_def
  set v : ℝ := max δ ((n : ℝ) + 1) with hv_def
  have ha : 0 < a := by rw [ha_def]; exact lt_min hδ (by positivity)
  have hav : a ≤ v := by rw [ha_def, hv_def]; exact min_le_max
  have hv0 : 0 ≤ v := le_of_lt (lt_of_lt_of_le ha hav)
  obtain ⟨N, C0, hC0, hrap⟩ :=
    B_uniform_rapid_bound D r b a v (j + 2) hD hr hb ha hav
  refine ⟨N, C0 * (v + 1) ^ j, by positivity, ?_⟩
  intro h hh hhc hsupp
  have hS : 0 ≤ Vendor.S b N h := Vendor.S_nonneg b hb N h hh
  have hδmem : δ ∈ Set.Icc a v :=
    ⟨by rw [ha_def]; exact min_le_left _ _, by rw [hv_def]; exact le_max_left _ _⟩
  have hmem : ((n : ℝ) + 1) ∈ Set.Icc a v :=
    ⟨by rw [ha_def]; exact min_le_right _ _, by rw [hv_def]; exact le_max_right _ _⟩
  have hA : 0 ≤ C0 * Vendor.S b N h * (v + 1) ^ j :=
    mul_nonneg (mul_nonneg (le_of_lt hC0) hS) (by positivity)
  have step : ∀ c ∈ Set.Icc a v, ∀ x : ℝ, 0 < x →
      ‖Vendor.EulerIter j (fieldTransform D r h) x‖
        ≤ C0 * (v + 1) ^ j * Vendor.S b N h * x ^ (-c) := by
    intro c hc x hx
    have hcpos : 0 < c := lt_of_lt_of_le ha hc.1
    have hcv : c ≤ v := hc.2
    rw [EulerIter_fieldTransform_eq_mellinInv D r h hD hr hh hhc j c x hcpos hx]
    have hbnd : ∀ t : ℝ,
        ‖(-(((c : ℂ) + (t : ℂ) * Complex.I))) ^ j
            * B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (C0 * Vendor.S b N h * (v + 1) ^ j) * (1 + |t|) ^ (-2 : ℝ) := by
      intro t
      have hrp := hrap h hh hhc hsupp c hc t
      have hs : ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ≤ (v + 1) * (1 + |t|) :=
        uniform_norm_add_mul_I_le c t v (le_of_lt hcpos) hcv hv0
      have hu : 0 < 1 + |t| := by positivity
      have hnorm :
          ‖(-(((c : ℂ) + (t : ℂ) * Complex.I))) ^ j
              * B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖
            = ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ j
              * ‖B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [norm_mul, norm_pow, norm_neg]
      rw [hnorm]
      have h1 : ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ j
              * ‖B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (v + 1) ^ j
              * ((1 + |t|) ^ j * ‖B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖) := by
        have hsp : ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ j ≤ (v + 1) ^ j * (1 + |t|) ^ j := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) hs j
        calc ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ j
              * ‖B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ ((v + 1) ^ j * (1 + |t|) ^ j)
                * ‖B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖ :=
              mul_le_mul_of_nonneg_right hsp (norm_nonneg _)
          _ = (v + 1) ^ j
                * ((1 + |t|) ^ j * ‖B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖) := by ring
      have h2 : (1 + |t|) ^ j * ‖B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (C0 * Vendor.S b N h) * (1 + |t|) ^ (-2 : ℝ) :=
        uniform_jet_mul_bound (1 + |t|) hu j (C0 * Vendor.S b N h)
          ‖B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖ hrp
      calc ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ j
              * ‖B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (v + 1) ^ j
              * ((1 + |t|) ^ j * ‖B D r h ((c : ℂ) + (t : ℂ) * Complex.I)‖) := h1
        _ ≤ (v + 1) ^ j * ((C0 * Vendor.S b N h) * (1 + |t|) ^ (-2 : ℝ)) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (C0 * Vendor.S b N h * (v + 1) ^ j) * (1 + |t|) ^ (-2 : ℝ) := by ring
    have hint : Integrable (fun t : ℝ =>
        (x : ℂ) ^ (-(c + (t : ℂ) * Complex.I))
          * ((-(((c : ℂ) + (t : ℂ) * Complex.I))) ^ j
              * B D r h ((c : ℂ) + (t : ℂ) * Complex.I))) := by
      simpa only [mul_assoc] using
        (B_euler_inverse_integrable D r h hD hr hh hhc j c x hcpos hx)
    have hmain := uniform_norm_mellinInv_le c x (C0 * Vendor.S b N h * (v + 1) ^ j)
      (fun s => (-s) ^ j * B D r h s) hx hA hint hbnd
    calc ‖mellinInv c (fun s => (-s) ^ j * B D r h s) x‖
        ≤ (C0 * Vendor.S b N h * (v + 1) ^ j) * x ^ (-c) := hmain
      _ = C0 * (v + 1) ^ j * Vendor.S b N h * x ^ (-c) := by ring
  refine ⟨?_, ?_⟩
  · intro x hx0 hx1
    simpa using step δ hδmem x hx0
  · intro x hx1
    have hlt : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    calc ‖Vendor.EulerIter j (fieldTransform D r h) x‖
        ≤ C0 * (v + 1) ^ j * Vendor.S b N h * x ^ (-(((n : ℝ) + 1))) :=
          step ((n : ℝ) + 1) hmem x hlt
      _ ≤ C0 * (v + 1) ^ j * Vendor.S b N h * x ^ (-(n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)

end DedekindZetaZeroFree.LargeSieve

end
