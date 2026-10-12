module

public import Mathlib.Analysis.MellinInversion

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

open MeasureTheory Set

namespace DedekindZetaZeroFree.LargeSieve.Vendor

theorem mellin_eq_of_eq_mellinInv (f : ℝ → ℂ) (A : ℂ → ℂ) (c : ℝ) (z : ℂ)
    (hz : z.re = c) (hf : MellinConvergent f z)
    (hA_cont : Continuous (fun t : ℝ => A ((c : ℂ) + (t : ℂ) * Complex.I)))
    (hA_int : Complex.VerticalIntegrable A c MeasureTheory.volume)
    (hInv : ∀ x : ℝ, 0 < x → f x = mellinInv c A x) :
    mellin f z = A z := by
  let q : ℝ → ℂ := fun y => A ((c : ℂ) + 2 * Real.pi * y * Complex.I)
  let g : ℝ → ℂ := fun u => Real.exp (-c * u) • f (Real.exp (-u))
  have hq : MeasureTheory.Integrable q := by
    convert hA_int.comp_mul_right' (show 2 * Real.pi ≠ 0 by positivity) using 1 <;>
      simp [q, Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
  have hqc : Continuous q := by
    convert hA_cont.comp (show Continuous (fun y : ℝ => 2 * Real.pi * y) by fun_prop) using 1
    funext y
    simp [q, Function.comp_def, Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
  have hreal : MellinConvergent f (c : ℂ) := by
    have hpow : ContinuousOn (fun x : ℝ => (x : ℂ) ^ ((c : ℂ) - z)) (Set.Ioi 0) :=
      continuousOn_of_forall_continuousAt fun x hx =>
        Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx.ne')
    have hb : ∀ᵐ x : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi 0),
        ‖(x : ℂ) ^ ((c : ℂ) - z)‖ ≤ 1 := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [hz]
    have hi := hf.bdd_mul (hpow.aestronglyMeasurable measurableSet_Ioi) hb
    apply hi.congr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [smul_eq_mul]
    rw [← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    congr 2
    ring
  have hg : MeasureTheory.Integrable g := by
    have he := (integrable_comp_exp
      (fun x : ℝ => (x : ℂ) ^ ((c : ℂ) - 1) • f x)).mpr hreal
    have heq : (fun u : ℝ => Real.exp u •
        ((Real.exp u : ℂ) ^ ((c : ℂ) - 1) • f (Real.exp u))) =
        (fun u : ℝ => Real.exp (c * u) • f (Real.exp u)) := by
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
  have hgeq : g = FourierTransform.fourierInv q := by
    funext u
    have hx := Real.exp_pos (-u)
    have hi := mellinInv_eq_fourierInv c A hx
    rw [← hInv _ hx] at hi
    dsimp [g]
    rw [hi, Real.log_exp, neg_neg]
    rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hx.le]
    rw [Real.rpow_def_of_pos hx, Real.log_exp]
    simp only [Complex.real_smul, smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    rw [show -c * u + -u * -c = 0 by ring]
    simp [q]
  have hFq : MeasureTheory.Integrable (FourierTransform.fourier q) := by
    have hinv : MeasureTheory.Integrable (FourierTransform.fourierInv q) := by rwa [← hgeq]
    have hn := hinv.comp_neg
    simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hn
  rw [mellin_eq_fourier, hz]
  change FourierTransform.fourier g (z.im / (2 * Real.pi)) = _
  rw [hgeq, hqc.fourier_fourierInv_eq hq hFq]
  dsimp [q]
  congr 1
  rw [show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_mul,
    mul_div_cancel₀ _ (show 2 * Real.pi ≠ 0 by positivity)]
  rw [← hz]
  exact Complex.re_add_im z

end DedekindZetaZeroFree.LargeSieve.Vendor
