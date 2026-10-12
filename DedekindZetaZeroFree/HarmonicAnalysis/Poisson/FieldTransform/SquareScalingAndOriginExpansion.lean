module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.UniformOriginRemainder
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.MellinSpectrumRecovery

@[expose] public section

noncomputable section
open scoped Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve

private lemma deriv_comp_sq (F : ℝ → ℂ) (x : ℝ) (hF : DifferentiableAt ℝ F (x ^ 2)) :
    deriv (fun y : ℝ => F (y ^ 2)) x = deriv F (x ^ 2) * (2 * x) := by
  have hsq : HasFDerivAt (fun y : ℝ => y ^ 2) (fderiv ℝ (fun y : ℝ => y ^ 2) x) x :=
    (differentiableAt_pow 2).hasFDerivAt
  have hF' : HasFDerivAt F (fderiv ℝ F (x ^ 2)) (x ^ 2) := hF.hasFDerivAt
  have hcomp : HasFDerivAt (fun y : ℝ => F (y ^ 2))
      ((fderiv ℝ F (x ^ 2)).comp (fderiv ℝ (fun y : ℝ => y ^ 2) x)) x :=
    HasFDerivAt.comp (f := fun y : ℝ => y ^ 2) x hF' hsq
  have h1 : deriv (fun y : ℝ => F (y ^ 2)) x =
      (fderiv ℝ F (x ^ 2)) (deriv (fun y : ℝ => y ^ 2) x) := by
    show (fderiv ℝ (fun y : ℝ => F (y ^ 2)) x : ℝ → ℂ) 1 = _
    rw [hcomp.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    rfl
  have hsq' : deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
    rw [deriv_pow_field 2]
    norm_num
  rw [h1, hsq', fderiv_eq_smul_deriv]
  simp only [Complex.real_smul]
  push_cast
  ring

private theorem eulerIter_contDiffOn {F : ℝ → ℂ} (hF : ContDiffOn ℝ ∞ F (Set.Ioi 0)) (i : ℕ) :
    ContDiffOn ℝ ∞ (Vendor.EulerIter i F) (Set.Ioi 0) := by
  induction i with
  | zero => exact hF
  | succ i ih =>
    have hderiv : ContDiffOn ℝ ∞ (deriv (Vendor.EulerIter i F)) (Set.Ioi 0) :=
      ih.deriv_of_isOpen isOpen_Ioi le_rfl
    have hlin : ContDiffOn ℝ ∞ (fun y : ℝ => (y : ℂ)) (Set.Ioi 0) :=
      Complex.ofRealCLM.contDiff.contDiffOn
    have hmul : ContDiffOn ℝ ∞
        (fun y : ℝ => (y : ℂ) * deriv (Vendor.EulerIter i F) y) (Set.Ioi 0) :=
      hlin.mul hderiv
    refine hmul.congr (fun y hy => ?_)
    exact Vendor.EulerIter_succ_of_pos i F y hy

private lemma differentiableAt_eulerIter {F : ℝ → ℂ} (hF : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (i : ℕ) {y : ℝ} (hy : 0 < y) : DifferentiableAt ℝ (Vendor.EulerIter i F) y :=
  ((eulerIter_contDiffOn hF i).differentiableOn (by simp)).differentiableAt
    (isOpen_Ioi.mem_nhds hy)

private lemma contDiffOn_eval_log (P : Polynomial ℂ) :
    ContDiffOn ℝ ∞ (fun y : ℝ => Polynomial.eval (Real.log y : ℂ) P) (Set.Ioi 0) := by
  have hq : ContDiffOn ℝ ∞ (fun y : ℝ => ((Real.log y : ℝ) : ℂ)) (Set.Ioi 0) :=
    (Complex.ofRealCLM.contDiff.contDiffOn).comp
      ((Real.contDiffOn_log (n := ∞)).mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
        exact hx.ne')) (fun y _ => Set.mem_univ _)
  have hsum : ContDiffOn ℝ ∞
      (fun y : ℝ => ∑ n ∈ P.support, P.coeff n * ((Real.log y : ℝ) : ℂ) ^ n)
      (Set.Ioi 0) :=
    ContDiffOn.sum (fun n _ => contDiffOn_const.mul (hq.pow n))
  refine hsum.congr (fun y _ => ?_)
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]

private lemma S_mono (b : ℝ) (hb : 0 < b) (N : ℕ) (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) :
    Vendor.S b N h ≤ Vendor.S b (N + 1) h := by
  unfold Vendor.S
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega)) ?_
  intro i _ _
  have hbd : BddAbove ((fun y : ℝ => ‖iteratedDeriv i h y‖) '' Set.Icc 0 b) :=
    (isCompact_Icc.image ((hh.continuous_iteratedDeriv i (by exact_mod_cast le_top)).norm)).bddAbove
  have hmem : ‖iteratedDeriv i h 0‖ ∈
      ((fun y : ℝ => ‖iteratedDeriv i h y‖) '' Set.Icc 0 b) :=
    ⟨0, ⟨le_rfl, le_of_lt hb⟩, rfl⟩
  exact le_trans (norm_nonneg _) (le_csSup hbd hmem)

private lemma eulerIter_eqOn_of_eqOn {f g : ℝ → ℂ}
    (h : Set.EqOn f g (Set.Ioi 0)) (j : ℕ) :
    Set.EqOn (Vendor.EulerIter j f) (Vendor.EulerIter j g) (Set.Ioi 0) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    intro y hy
    rw [Vendor.EulerIter_succ_of_pos j f y hy, Vendor.EulerIter_succ_of_pos j g y hy,
      ih.deriv isOpen_Ioi hy]

private lemma eulerIter_comp_sq {F : ℝ → ℂ} (hF : ContDiffOn ℝ ∞ F (Set.Ioi 0)) :
    ∀ (j : ℕ) (x : ℝ), 0 < x →
      Vendor.EulerIter j (fun y : ℝ => F (y ^ 2)) x =
        (2 : ℂ) ^ j * Vendor.EulerIter j F (x ^ 2) := by
  intro j
  induction j with
  | zero => intro x hx; simp
  | succ j ih =>
    intro x hx
    have hev : (Vendor.EulerIter j (fun z : ℝ => F (z ^ 2))) =ᶠ[nhds x]
        (fun y : ℝ => (2 : ℂ) ^ j * Vendor.EulerIter j F (y ^ 2)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact ih y hy
    rw [Vendor.EulerIter_succ_of_pos j (fun z : ℝ => F (z ^ 2)) x hx, hev.deriv_eq,
      deriv_const_mul_field, deriv_comp_sq (Vendor.EulerIter j F) x
        (differentiableAt_eulerIter hF j (pow_pos hx 2)),
      Vendor.EulerIter_succ_of_pos j F (x ^ 2) (pow_pos hx 2)]
    generalize hd : deriv (Vendor.EulerIter j F) (x ^ 2) = d
    rw [pow_succ]
    push_cast
    ring

theorem EulerIter_fieldTransform_comp_sq_sub_originPolynomial_eq
    (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (j : ℕ) (x : ℝ) (hx : 0 < x) :
    Vendor.EulerIter j (fun y : ℝ => fieldTransform D r h (y ^ 2) -
      Polynomial.eval ((2 * Real.log y : ℝ) : ℂ) (originPolynomial D r h)) x =
        (2 : ℂ) ^ j *
          Vendor.EulerIter j (fun y : ℝ => fieldTransform D r h y -
            Polynomial.eval (Real.log y : ℂ) (originPolynomial D r h)) (x ^ 2) := by
  have hR : ContDiffOn ℝ ∞
      (fun y : ℝ => fieldTransform D r h y -
        Polynomial.eval (Real.log y : ℂ) (originPolynomial D r h)) (Set.Ioi 0) :=
    (fieldTransform_contDiffOn D r h hD hr hh hhc).sub (contDiffOn_eval_log _)
  have hEqOn : Set.EqOn
      (fun y : ℝ => fieldTransform D r h (y ^ 2) -
        Polynomial.eval ((2 * Real.log y : ℝ) : ℂ) (originPolynomial D r h))
      (fun y : ℝ => fieldTransform D r h (y ^ 2) -
        Polynomial.eval (Real.log (y ^ 2) : ℂ) (originPolynomial D r h)) (Set.Ioi 0) := by
    intro y hy
    have hlog : ((2 * Real.log y : ℝ) : ℂ) = (Real.log (y ^ 2) : ℂ) := by
      rw [Real.log_pow]; push_cast; ring
    simp only [hlog]
  rw [eulerIter_eqOn_of_eqOn hEqOn j hx]
  exact eulerIter_comp_sq hR j x hx

theorem fieldTransform_comp_sq_origin_remainder_uniform_bound
    (D : ℝ) (r : ℕ) (b δ : ℝ) (j : ℕ)
    (hD : 0 < D) (hr : 1 ≤ r) (hb : 0 < b)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ (N : ℕ) (C : ℝ), 0 < N ∧ 0 < C ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
        (∀ x : ℝ, b < x → h x = 0) →
        ∀ x : ℝ, 0 < x → x ≤ 1 →
          ‖Vendor.EulerIter j (fun y : ℝ => fieldTransform D r h (y ^ 2) -
            Polynomial.eval ((2 * Real.log y : ℝ) : ℂ) (originPolynomial D r h)) x‖ ≤
              C * Vendor.S b N h * x ^ (2 * δ) := by
  obtain ⟨N, C, hC, hbd⟩ :=
    fieldTransform_origin_remainder_uniform_bound D r b δ j hD hr hb hδ hδ1
  refine ⟨N + 1, (2 : ℝ) ^ j * C, by omega, mul_pos (pow_pos (by norm_num) j) hC, ?_⟩
  intro h hh hhc hsupp x hx hx1
  rw [EulerIter_fieldTransform_comp_sq_sub_originPolynomial_eq D r h hD hr hh hhc j x hx,
    norm_mul, norm_pow, Complex.norm_ofNat]
  have hx2 : 0 < x ^ 2 := pow_pos hx 2
  have hx21 : x ^ 2 ≤ 1 := by nlinarith
  have hb' := hbd h hh hhc hsupp (x ^ 2) hx2 hx21
  have hrpow : (x ^ 2) ^ δ = x ^ (2 * δ) := by
    rw [show x ^ 2 = x ^ (2 : ℝ) by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
    rw [← Real.rpow_mul hx.le]
  rw [hrpow] at hb'
  have hS := S_mono b hb N h hh
  calc (2 : ℝ) ^ j * ‖Vendor.EulerIter j (fun y : ℝ => fieldTransform D r h y -
        Polynomial.eval (Real.log y : ℂ) (originPolynomial D r h)) (x ^ 2)‖
      ≤ (2 : ℝ) ^ j * (C * Vendor.S b (N + 1) h * x ^ (2 * δ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ‖Vendor.EulerIter j (fun y : ℝ => fieldTransform D r h y -
              Polynomial.eval (Real.log y : ℂ) (originPolynomial D r h)) (x ^ 2)‖
            ≤ C * Vendor.S b N h * x ^ (2 * δ) := hb'
          _ ≤ C * Vendor.S b (N + 1) h * x ^ (2 * δ) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hC.le)
                (Real.rpow_nonneg hx.le _)
    _ = ((2 : ℝ) ^ j * C) * Vendor.S b (N + 1) h * x ^ (2 * δ) := by ring

end DedekindZetaZeroFree.LargeSieve

end
