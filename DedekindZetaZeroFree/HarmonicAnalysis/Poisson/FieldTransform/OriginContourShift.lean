module

public import DedekindZetaZeroFree.Analysis.ContourIntegration.FiniteOrderPole
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.OriginLaurentAndLogarithmicResidues
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.NegativeStripBounds
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.EulerDerivativesAndDecay

@[expose] public section

noncomputable section
open scoped Classical ContDiff Topology
open MeasureTheory Filter

namespace DedekindZetaZeroFree.LargeSieve

def originPolynomial (D : ℝ) (r : ℕ) (h : ℝ → ℂ) : Polynomial ℂ :=
  Vendor.originLogResiduePolynomial (A D r h) r

private lemma exists_support_bound {h : ℝ → ℂ} (hhc : HasCompactSupport h) :
    ∃ b : ℝ, 0 < b ∧ ∀ x : ℝ, b < x → h x = 0 := by
  obtain ⟨b, hb⟩ := hhc.bddAbove
  refine ⟨max b 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx => ?_⟩
  refine Function.notMem_support.mp fun hmem =>
    absurd (hb (subset_tsupport h hmem)) (not_le.mpr (lt_of_le_of_lt (le_max_left _ _) hx))

private lemma neg_vertical_re (σ t : ℝ) :
    (-((σ : ℂ) + (t : ℂ) * Complex.I)).re = -σ := by
  simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private lemma contDiffOn_polynomial_eval_log (P : Polynomial ℂ) :
    ContDiffOn ℝ ∞ (fun y : ℝ => Polynomial.eval (Real.log y : ℂ) P) (Set.Ioi 0) := by
  have hlog : ContDiffOn ℝ ∞ Real.log {0}ᶜ := Real.contDiffOn_log
  have h1 : ContDiffOn ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) (Set.Ioi 0) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hlog).mono
      (by intro x hx; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hx)
  have h2 : ContDiffOn ℝ ∞ (fun z : ℂ => Polynomial.eval z P) Set.univ :=
    ((Polynomial.contDiff_aeval (𝕜 := ℂ) P ∞).restrict_scalars ℝ).contDiffOn
  exact h2.comp h1 (Set.mapsTo_univ _ _)

private lemma differentiableOn_twisted (A : ℂ → ℂ) (U : Set ℂ) (hA : AnalyticOnNhd ℂ A U)
    (L : ℝ) (j r : ℕ) :
    DifferentiableOn ℂ
      (fun s : ℂ => Complex.exp (-s * (L : ℂ)) * ((-s) ^ j * (A s / s ^ r))) (U \ {0}) := by
  have hexp : DifferentiableOn ℂ (fun s : ℂ => Complex.exp (-s * (L : ℂ))) (U \ {0}) :=
    (Complex.differentiable_exp (𝕜 := ℂ)).differentiableOn.comp
      ((differentiable_id.neg.mul_const (L : ℂ)).differentiableOn) (Set.mapsTo_univ _ _)
  have hpow : DifferentiableOn ℂ (fun s : ℂ => (-s) ^ j) (U \ {0}) :=
    (differentiable_id.neg.differentiableOn).pow j
  have hdiv : DifferentiableOn ℂ (fun s : ℂ => A s / s ^ r) (U \ {0}) :=
    (hA.differentiableOn.mono Set.diff_subset).div
      ((differentiable_id.differentiableOn).pow r) (fun s hs => pow_ne_zero _ hs.2)
  exact hexp.mul (hpow.mul hdiv)

private lemma eulerIter_contDiffOn (j : ℕ) {g : ℝ → ℂ}
    (hg : ContDiffOn ℝ ∞ g (Set.Ioi 0)) :
    ContDiffOn ℝ ∞ (Vendor.EulerIter j g) (Set.Ioi 0) := by
  induction j with
  | zero => simpa using hg
  | succ j ih =>
    rw [show Vendor.EulerIter (j + 1) g =
      fun y : ℝ => if 0 < y then (y : ℂ) * deriv (Vendor.EulerIter j g) y else 0 from rfl]
    have hderiv : ContDiffOn ℝ ∞ (deriv (Vendor.EulerIter j g)) (Set.Ioi 0) :=
      (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp ih |>.2
    have hprod : ContDiffOn ℝ ∞ (fun y : ℝ => (y : ℂ) * deriv (Vendor.EulerIter j g) y)
        (Set.Ioi 0) :=
      ContDiffOn.mul (Complex.ofRealCLM.contDiff.contDiffOn) hderiv
    exact (contDiffOn_congr (s := Set.Ioi 0)
      (f₁ := fun y : ℝ => (y : ℂ) * deriv (Vendor.EulerIter j g) y)
      (f := fun y : ℝ => if 0 < y then (y : ℂ) * deriv (Vendor.EulerIter j g) y else 0)
      (fun y hy => (if_pos hy).symm)).mp hprod

private lemma eulerIter_sub (j : ℕ) {g₁ g₂ : ℝ → ℂ}
    (h₁ : ContDiffOn ℝ ∞ g₁ (Set.Ioi 0)) (h₂ : ContDiffOn ℝ ∞ g₂ (Set.Ioi 0)) :
    ∀ x : ℝ, 0 < x → Vendor.EulerIter j (fun y : ℝ => g₁ y - g₂ y) x =
      Vendor.EulerIter j g₁ x - Vendor.EulerIter j g₂ x := by
  induction j with
  | zero => intro x hx; rfl
  | succ j ih =>
    intro x hx
    rw [Vendor.EulerIter_succ_of_pos j (fun y : ℝ => g₁ y - g₂ y) x hx,
      Vendor.EulerIter_succ_of_pos j g₁ x hx, Vendor.EulerIter_succ_of_pos j g₂ x hx]
    have hd₁ : DifferentiableAt ℝ (Vendor.EulerIter j g₁) x :=
      ((eulerIter_contDiffOn j h₁).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds hx)
    have hd₂ : DifferentiableAt ℝ (Vendor.EulerIter j g₂) x :=
      ((eulerIter_contDiffOn j h₂).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds hx)
    have heq : Vendor.EulerIter j (fun y : ℝ => g₁ y - g₂ y) =ᶠ[𝓝 x]
        (Vendor.EulerIter j g₁ - Vendor.EulerIter j g₂) :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hx) fun y hy => ih y hy
    rw [heq.deriv_eq, deriv_sub hd₁ hd₂]
    ring

theorem originPolynomial_natDegree_le (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) :
    (originPolynomial D r h).natDegree ≤ r - 1 := by
  exact Vendor.originLogResiduePolynomial_natDegree_le (A D r h) r hr

theorem originPolynomial_coeff_top (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) :
    (originPolynomial D r h).coeff (r - 1) =
      (-1 : ℂ) ^ (r - 1) * (D : ℂ) ^ (-(1 / 2 : ℂ)) *
        (((2 * Real.pi : ℝ) : ℂ) ^ r) * mellin h 1 /
          ((r - 1).factorial : ℂ) := by
  simp only [originPolynomial]
  rw [Vendor.originLogResiduePolynomial_coeff_top (A D r h) r hr,
    A_zero D r h hD hr hh hhc]
  ring

theorem B_euler_negative_inverse_integrable
    (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (j : ℕ) (δ x : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hx : 0 < x) :
    MeasureTheory.Integrable (fun t : ℝ =>
      (x : ℂ) ^ (-((-δ : ℂ) + (t : ℂ) * Complex.I)) *
        (-((-δ : ℂ) + (t : ℂ) * Complex.I)) ^ j *
          B D r h ((-δ : ℂ) + (t : ℂ) * Complex.I))
      MeasureTheory.volume := by
  obtain ⟨b, hb, hsupp⟩ := exists_support_bound hhc
  obtain ⟨N, C, hC, hbd⟩ :=
    B_negative_line_uniform_integral_bound D r b δ j hD hr hb hδ hδ1
  have hint : MeasureTheory.Integrable (fun t : ℝ =>
      (-((-δ : ℂ) + (t : ℂ) * Complex.I)) ^ j *
        B D r h ((-δ : ℂ) + (t : ℂ) * Complex.I)) MeasureTheory.volume :=
    (hbd h hh hhc hsupp).1
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (x : ℂ) ^ (-((-δ : ℂ) + (t : ℂ) * Complex.I))) MeasureTheory.volume :=
    ((continuous_iff_continuousAt.mpr fun z =>
      (by fun_prop : Continuous fun t : ℝ => -((-δ : ℂ) + (t : ℂ) * Complex.I)) |>.continuousAt |>.const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))))).aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' (hint.norm.const_mul (x ^ δ))
    (by
      refine (hmeas.mul hint.aestronglyMeasurable).congr ?_
      filter_upwards with t
      exact (mul_assoc _ _ _).symm) ?_
  filter_upwards with t
  have hre : (-((-δ : ℂ) + (t : ℂ) * Complex.I)).re = δ := by
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  simp only [norm_mul, norm_pow, norm_neg, mul_assoc,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
  exact le_refl _

theorem EulerIter_fieldTransform_sub_originPolynomial_eq_mellinInv
    (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (j : ℕ) (δ x : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hx : 0 < x) :
    Vendor.EulerIter j (fun y : ℝ => fieldTransform D r h y -
      Polynomial.eval (Real.log y : ℂ) (originPolynomial D r h)) x =
        mellinInv (-δ) (fun s : ℂ => (-s) ^ j * B D r h s) x := by
  set F : ℂ → ℂ := fun s => (x : ℂ) ^ (-s) * ((-s) ^ j * B D r h s) with hFdef

  have hUopen : IsOpen {s : ℂ | -1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hU0 : (0 : ℂ) ∈ {s : ℂ | -1 < s.re} := by simp
  have hAan : AnalyticOnNhd ℂ (A D r h) {s : ℂ | -1 < s.re} :=
    A_analyticOnNhd D r h hD hr hh hhc
  obtain ⟨cc, G, hGan, hGid, hc1⟩ :=
    Vendor.origin_exists_analytic_twisted_laurent {s : ℂ | -1 < s.re} hUopen hU0
      (A D r h) hAan r hr (Real.log x) j

  have hstrip : {s : ℂ | -δ ≤ s.re ∧ s.re ≤ 1} ⊆ {s : ℂ | -1 < s.re} := by
    intro s hs
    simp only [Set.mem_setOf_eq] at hs ⊢
    linarith [hs.1]

  have hFdiff : DifferentiableOn ℂ F ({s : ℂ | -1 < s.re} \ {(0 : ℂ)}) := by
    refine (differentiableOn_twisted (A D r h) {s : ℂ | -1 < s.re} hAan (Real.log x) j r).congr
      fun s hs => ?_
    simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff] at hs
    obtain ⟨hsre, hs0⟩ := hs
    show (x : ℂ) ^ (-s) * ((-s) ^ j * B D r h s) =
      Complex.exp (-s * (Real.log x : ℂ)) * ((-s) ^ j * (A D r h s / s ^ r))
    have hcpow : (x : ℂ) ^ (-s) = Complex.exp (-s * (Real.log x : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx)),
        ← Complex.ofReal_log (le_of_lt hx), mul_comm]
    rw [hcpow, B_eq_A_div D r h hD hr hh hhc s hsre hs0]

  have hregular : ∃ (G' : ℂ → ℂ) (U : Set ℂ), IsOpen U ∧
      {s : ℂ | -δ ≤ s.re ∧ s.re ≤ 1} ⊆ U ∧
      DifferentiableOn ℂ G' U ∧
      ∀ s : ℂ, -δ ≤ s.re → s.re ≤ 1 → s ≠ 0 →
        F s = G' s + ∑ m ∈ Finset.Icc 1 r, cc m / (s - (0 : ℂ)) ^ m := by
    refine ⟨G, {s : ℂ | -1 < s.re}, hUopen, hstrip, hGan.differentiableOn, ?_⟩
    intro s hs1 hs2 hs0
    have hsre : -1 < s.re := by linarith
    have hid := hGid s (by simp only [Set.mem_setOf_eq]; exact hsre) hs0
    show (x : ℂ) ^ (-s) * ((-s) ^ j * B D r h s) =
      G s + ∑ m ∈ Finset.Icc 1 r, cc m / (s - (0 : ℂ)) ^ m
    have hcpow : (x : ℂ) ^ (-s) = Complex.exp (-s * (Real.log x : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx)),
        ← Complex.ofReal_log (le_of_lt hx), mul_comm]
    rw [hcpow, B_eq_A_div D r h hD hr hh hhc s hsre hs0]
    have hgoal : Complex.exp (-s * (Real.log x : ℂ)) * ((-s) ^ j * (A D r h s / s ^ r)) =
        (-s) ^ j * Complex.exp (-s * (Real.log x : ℂ)) * A D r h s / s ^ r := by
      ring
    rw [hgoal, hid]
    simp only [sub_zero]

  have ha : Complex.VerticalIntegrable F (-δ) := by
    simpa only [Complex.VerticalIntegrable, hFdef, mul_assoc, Complex.ofReal_neg] using
      B_euler_negative_inverse_integrable D r h hD hr hh hhc j δ x hδ hδ1 hx
  have hb : Complex.VerticalIntegrable F 1 := by
    simpa only [Complex.VerticalIntegrable, hFdef, mul_assoc, Complex.ofReal_neg] using
      B_euler_inverse_integrable D r h hD hr hh hhc j 1 x (by norm_num) hx

  have hgrowth : ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ σ : ℝ, σ ∈ Set.Icc (-δ) 1 → ∀ t : ℝ, 1 ≤ |t| →
        ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ k := by
    obtain ⟨b, hb0, hsupp⟩ := exists_support_bound hhc
    obtain ⟨N, C₀, hC₀, hbd⟩ :=
      B_uniform_rapid_bound_negative_strip D r b (-δ) 1 j hD hr hb0 (by linarith) (by linarith)
    have hS : 0 ≤ Vendor.S b N h := Vendor.S_nonneg b hb0 N h hh
    have hXnn : 0 ≤ max (x ^ (-1 : ℝ)) (x ^ δ) :=
      le_max_iff.mpr (Or.inl (Real.rpow_nonneg (le_of_lt hx) _))
    refine ⟨max (x ^ (-1 : ℝ)) (x ^ δ) * (C₀ * Vendor.S b N h), j,
      mul_nonneg hXnn (mul_nonneg (le_of_lt hC₀) hS), ?_⟩
    intro σ hσ t ht
    have hX : x ^ (-σ) ≤ max (x ^ (-1 : ℝ)) (x ^ δ) := by
      rcases lt_or_ge x 1 with hx1 | hx1
      · exact le_trans (Real.rpow_le_rpow_of_exponent_ge hx (le_of_lt hx1)
          (by linarith [hσ.2])) (le_max_left _ _)
      · exact le_trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hσ.1]))
          (le_max_right _ _)
    have hB : ‖B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C₀ * Vendor.S b N h := by
      have h1 := hbd h hh hhc hsupp σ hσ t ht
      calc ‖B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          = 1 * ‖B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := (one_mul _).symm
        _ ≤ (1 + |t|) ^ j * ‖B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
            mul_le_mul_of_nonneg_right
              (one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg t))) (norm_nonneg _)
        _ ≤ C₀ * Vendor.S b N h := h1
    have hnorm2 : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ 1 + |t| := by
      calc ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ :=
            norm_add_le _ _
        _ = |σ| + |t| := by simp
        _ ≤ 1 + |t| := by
            have h1 : |σ| ≤ 1 := by
              rw [abs_le]
              exact ⟨by linarith [hσ.1, hδ], by linarith [hσ.2, hδ1]⟩
            linarith
    have hnorm : ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
        x ^ (-σ) * (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ j *
          ‖B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
      rw [hFdef]
      rw [norm_mul, norm_mul, norm_pow, norm_neg,
        Complex.norm_cpow_eq_rpow_re_of_pos hx, neg_vertical_re]
    rw [hnorm]
    calc x ^ (-σ) * (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ j *
          ‖B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖)
        ≤ max (x ^ (-1 : ℝ)) (x ^ δ) * ((1 + |t|) ^ j * (C₀ * Vendor.S b N h)) :=
          mul_le_mul hX
            (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hnorm2 j) hB (norm_nonneg _)
              (pow_nonneg (by positivity) _))
            (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)) hXnn
      _ = max (x ^ (-1 : ℝ)) (x ^ δ) * (C₀ * Vendor.S b N h) * (1 + |t|) ^ j := by ring
  have hcontour : Vendor.verticalIntegral 1 F = Vendor.verticalIntegral (-δ) F + cc 1 := by
    have h := Vendor.verticalIntegral_sub_eq_of_finite_order_pole (a := -δ) (b := 1) (p := 0)
      (r := r) (c := cc) (F := F) (by linarith) (by norm_num) hr
      ⟨{s : ℂ | -1 < s.re}, hUopen, hstrip, hFdiff⟩ hregular ha hb hgrowth
    rwa [sub_eq_iff_eq_add, add_comm] at h
  have hV1 : Vendor.verticalIntegral 1 F = mellinInv 1 (fun s : ℂ => (-s) ^ j * B D r h s) x := by
    rw [hFdef]
    exact (Vendor.mellinInv_eq_verticalIntegral 1 (fun s : ℂ => (-s) ^ j * B D r h s) hx).symm
  have hVδ : Vendor.verticalIntegral (-δ) F = mellinInv (-δ) (fun s : ℂ => (-s) ^ j * B D r h s) x := by
    rw [hFdef]
    exact (Vendor.mellinInv_eq_verticalIntegral (-δ) (fun s : ℂ => (-s) ^ j * B D r h s) hx).symm
  have hcc1 : cc 1 = Polynomial.eval (Real.log x : ℂ)
      ((Polynomial.derivative^[j]) (originPolynomial D r h)) := by
    rw [hc1]
    simp only [originPolynomial]
  have hEulerF := EulerIter_fieldTransform_eq_mellinInv D r h hD hr hh hhc j 1 x (by norm_num) hx
  have hEulerP := Vendor.EulerIter_eval_log_polynomial (originPolynomial D r h) j x hx
  have hsub := eulerIter_sub j (fieldTransform_contDiffOn D r h hD hr hh hhc)
    (contDiffOn_polynomial_eval_log (originPolynomial D r h)) x hx
  calc Vendor.EulerIter j (fun y : ℝ => fieldTransform D r h y -
        Polynomial.eval (Real.log y : ℂ) (originPolynomial D r h)) x
      = Vendor.EulerIter j (fieldTransform D r h) x -
        Vendor.EulerIter j (fun y : ℝ => Polynomial.eval (Real.log y : ℂ)
          (originPolynomial D r h)) x := hsub
    _ = mellinInv 1 (fun s : ℂ => (-s) ^ j * B D r h s) x -
        Polynomial.eval (Real.log x : ℂ) ((Polynomial.derivative^[j])
          (originPolynomial D r h)) := by rw [hEulerF, hEulerP]
    _ = Vendor.verticalIntegral 1 F - cc 1 := by rw [hV1, hcc1]
    _ = Vendor.verticalIntegral (-δ) F := by rw [sub_eq_iff_eq_add]; exact hcontour
    _ = mellinInv (-δ) (fun s : ℂ => (-s) ^ j * B D r h s) x := hVδ

end DedekindZetaZeroFree.LargeSieve

end
