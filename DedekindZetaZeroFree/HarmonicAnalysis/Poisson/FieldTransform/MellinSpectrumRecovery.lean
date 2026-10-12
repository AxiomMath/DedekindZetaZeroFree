module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.EulerDerivativesAndDecay

@[expose] public section

open MeasureTheory Set Filter Asymptotics

noncomputable section
open scoped Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve

theorem fieldTransform_mellinConvergent
    (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (fieldTransform D r h) s := by
  have hf_loc : LocallyIntegrableOn (fieldTransform D r h) (Set.Ioi 0) :=
    (fieldTransform_contDiffOn D r h hD hr hh hhc).continuousOn.locallyIntegrableOn
      measurableSet_Ioi
  have hδ : 0 < s.re / 2 := by linarith
  obtain ⟨C, _hCpos, hbot, htop⟩ :=
    fieldTransform_euler_two_ended_bound D r h hD hr hh hhc 0 (Nat.ceil s.re + 1)
      (s.re / 2) hδ
  simp only [Vendor.EulerIter_zero] at hbot htop
  refine mellinConvergent_of_isBigO_rpow (a := (Nat.ceil s.re + 1 : ℝ)) (b := s.re / 2)
    hf_loc ?_ ?_ ?_ ?_
  · refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ x) _)]
    simpa using htop x hx1
  · have h1 := Nat.le_ceil s.re
    have h2 : s.re < (Nat.ceil s.re : ℝ) + 1 := by linarith
    simpa using h2
  · refine IsBigO.of_bound C ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
    exact hbot x hx hx1.le
  · linarith

theorem mellin_fieldTransform_eq_B
    (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (s : ℂ) (hs : 0 < s.re) :
    mellin (fieldTransform D r h) s = B D r h s := by
  let f : ℝ → ℂ := fun y => B D r h ((s.re : ℂ) + 2 * Real.pi * y * Complex.I)
  let g : ℝ → ℂ := fun u => Real.exp (-s.re * u) •
    fieldTransform D r h (Real.exp (-u))
  have hf : Integrable f := by
    have hb := B_inverse_integrable D r h hD hr hh hhc s.re 1 hs (by norm_num)
    have hb' : Integrable (fun t : ℝ => B D r h ((s.re : ℂ) + t * Complex.I)) := by
      simpa using hb
    convert hb'.comp_mul_right' (show 2 * Real.pi ≠ 0 by positivity) using 1 <;>
      simp [f, Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
  have hfc : Continuous f :=
    (B_differentiableOn D r h hD hr hh hhc).continuousOn.comp_continuous
      (by fun_prop) (fun y => by simpa using hs)
  have hg : Integrable g := by
    have hm := fieldTransform_mellinConvergent D r h hD hr hh hhc (s.re : ℂ) hs
    have he := (integrable_comp_exp
      (fun x : ℝ => (x : ℂ) ^ ((s.re : ℂ) - 1) • fieldTransform D r h x)).mpr hm
    have heq : (fun u : ℝ => Real.exp u •
        ((Real.exp u : ℂ) ^ ((s.re : ℂ) - 1) • fieldTransform D r h (Real.exp u))) =
        (fun u : ℝ => Real.exp (s.re * u) • fieldTransform D r h (Real.exp u)) := by
      funext u
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
        ← Complex.ofReal_cpow (Real.exp_pos u).le]
      simp only [Complex.real_smul, smul_eq_mul]
      rw [← mul_assoc, ← Complex.ofReal_mul]
      congr 2
      rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, ← Real.exp_add]
      congr 1
      ring
    rw [heq] at he
    simpa [g] using he.comp_neg
  have hgeq : g = FourierTransform.fourierInv f := by
    funext u
    have hx := Real.exp_pos (-u)
    have hi := mellinInv_eq_fourierInv s.re (B D r h) hx
    rw [B_mellinInv_eq D r h hD hr hh hhc s.re (Real.exp (-u)) hs hx] at hi
    dsimp [g]
    rw [fieldTransform, if_pos hx, hi]
    rw [Real.log_exp, neg_neg]
    rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hx.le]
    rw [Real.rpow_def_of_pos hx, Real.log_exp]
    simp only [Complex.real_smul, smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    rw [show -s.re * u + -u * -s.re = 0 by ring]
    simp [f]
  have hFf : Integrable (FourierTransform.fourier f) := by
    have hinv : Integrable (FourierTransform.fourierInv f) := by rwa [← hgeq]
    have hn := hinv.comp_neg
    simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hn
  rw [mellin_eq_fourier]
  change FourierTransform.fourier g (s.im / (2 * Real.pi)) = _
  rw [hgeq, hfc.fourier_fourierInv_eq hf hFf]
  dsimp [f]
  congr 1
  rw [show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_mul,
    mul_div_cancel₀ _ (show 2 * Real.pi ≠ 0 by positivity)]
  exact Complex.re_add_im s

end DedekindZetaZeroFree.LargeSieve

end
