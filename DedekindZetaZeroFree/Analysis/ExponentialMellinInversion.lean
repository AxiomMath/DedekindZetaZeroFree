module

public import Mathlib.Analysis.MellinInversion
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.GammaVerticalMoments

@[expose] public section

namespace DedekindZetaZeroFree

open MeasureTheory

private lemma exp_inversion_gamma_continuous :
    Continuous (fun t : ℝ => Complex.Gamma (2 + (t : ℂ) * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt)
  intro n hn
  have hr := congrArg Complex.re hn
  simp at hr
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private lemma exp_inversion_gamma_integrable :
    Integrable (fun t : ℝ => Complex.Gamma (2 + (t : ℂ) * Complex.I)) := by
  obtain ⟨C, hC, h⟩ := detector_sz_gamma_moments 0 le_rfl
  have hi := (h 2 (Set.mem_union_right _ (by simp)) 0).1
  have hn : Integrable (fun t : ℝ => ‖Complex.Gamma (2 + (t : ℂ) * Complex.I)‖) := by
    simpa using hi
  exact (integrable_norm_iff exp_inversion_gamma_continuous.aestronglyMeasurable).mp hn

theorem detector_sz_exp_inversion_integrable
    (x : ℝ) (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      Complex.Gamma (2 + (t : ℂ) * Complex.I) *
        (x : ℂ) ^ (-(2 + (t : ℂ) * Complex.I))) := by
  have hp : Continuous (fun t : ℝ =>
      (x : ℂ) ^ (-(2 + (t : ℂ) * Complex.I))) :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hi := exp_inversion_gamma_integrable.norm.mul_const (x ^ (-2 : ℝ))
  apply hi.mono' (exp_inversion_gamma_continuous.mul hp).aestronglyMeasurable
  filter_upwards [] with t
  dsimp only [Pi.mul_apply]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem detector_sz_exp_inversion
    (x : ℝ) (hx : 0 < x) :
    (Real.exp (-x) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, Complex.Gamma (2 + (t : ℂ) * Complex.I) *
        (x : ℂ) ^ (-(2 + (t : ℂ) * Complex.I)) := by
  have hline (t : ℝ) :
      mellin (fun y : ℝ => (Real.exp (-y) : ℂ)) (2 + (t : ℂ) * Complex.I) =
        Complex.Gamma (2 + (t : ℂ) * Complex.I) := by
    rw [← Complex.GammaIntegral_eq_mellin, Complex.Gamma_eq_integral (by simp)]
  have hf : MellinConvergent (fun y : ℝ => (Real.exp (-y) : ℂ)) 2 := by
    simpa [MellinConvergent, smul_eq_mul, mul_comm] using
      (Complex.GammaIntegral_convergent (s := 2) (by norm_num))
  have hF : Complex.VerticalIntegrable
      (mellin (fun y : ℝ => (Real.exp (-y) : ℂ))) 2 := by
    simpa only [Complex.VerticalIntegrable, Complex.ofReal_ofNat, hline] using
      exp_inversion_gamma_integrable
  have hfx : ContinuousAt (fun y : ℝ => (Real.exp (-y) : ℂ)) x := by
    fun_prop
  have hi := (mellinInv_mellin_eq 2 (fun y : ℝ => (Real.exp (-y) : ℂ)) hx hf hF hfx).symm
  simp only [mellinInv, Complex.ofReal_ofNat, smul_eq_mul, Complex.real_smul] at hi
  simp_rw [hline] at hi
  simpa only [mul_comm] using hi

end DedekindZetaZeroFree
