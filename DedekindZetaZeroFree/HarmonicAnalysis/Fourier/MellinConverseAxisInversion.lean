module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree

open MeasureTheory
open scoped FourierTransform

theorem mellin_converse_axis_inversion
    (c : ℝ) (g : ℝ → ℂ) (G : ℂ → ℂ)
    (hc : 1 < c) (hg_cont : ContinuousOn g (Set.Ioi 0))
    (hg_mellin : MellinConvergent g (-(c : ℂ)))
    (hG_int : Integrable (fun t : ℝ => G ((c : ℂ) + t * Complex.I)))
    (hG_cont : Continuous (fun t : ℝ => G ((c : ℂ) + t * Complex.I)))
    (hg_inv : ∀ x : ℝ, 0 < x → g x = mellinInv (-c) (fun z : ℂ => G (-z)) x) :
    ∀ t : ℝ, mellin g (-((c : ℂ) + t * Complex.I)) = G ((c : ℂ) + t * Complex.I) := by
  classical
  let p : ℝ → ℂ := fun u => Real.exp (c * u) • g (Real.exp (-u))
  let F : ℝ → ℂ := fun y => G ((c : ℂ) - (2 * Real.pi * y : ℝ) * Complex.I)
  have hp_int : Integrable p := by
    have h : Integrable (fun u : ℝ => Real.exp u •
        ((Real.exp u : ℂ) ^ (-(c : ℂ) - 1) • g (Real.exp u))) :=
      (integrable_comp_exp _).mpr hg_mellin
    have hpoint (u : ℝ) : Real.exp u •
        ((Real.exp u : ℂ) ^ (-(c : ℂ) - 1) • g (Real.exp u)) =
        Real.exp (-(c * u)) • g (Real.exp u) := by
      have hexp : (-(c : ℂ) - 1) = ((-c - 1 : ℝ) : ℂ) := by push_cast; rfl
      rw [hexp, ← Complex.ofReal_cpow (le_of_lt (Real.exp_pos _)), ← Real.exp_mul]
      rw [← smul_assoc, Complex.real_smul, ← Complex.ofReal_mul, ← Real.exp_add]
      have hsum : u + u * (-c - 1) = -(c * u) := by ring
      rw [hsum]
      rfl
    have hh : Integrable (fun u : ℝ => Real.exp (-(c * u)) • g (Real.exp u)) := by
      convert h using 1
      funext u
      exact (hpoint u).symm
    convert hh.comp_neg using 1
    funext u
    simp only [p, neg_mul, neg_neg]
    congr 2 <;> ring
  have hF_int : Integrable F := by
    have h := hG_int.comp_mul_right' (show -(2 * Real.pi) ≠ 0 by simp)
    convert h using 1
    funext y
    simp only [F]
    congr 1
    push_cast
    ring
  have hp_eq (u : ℝ) : p u = 𝓕⁻ F u := by
    dsimp only [p]
    rw [hg_inv _ (Real.exp_pos _), mellinInv_eq_fourierInv _ _ (Real.exp_pos _)]
    simp only [Real.log_exp, neg_neg]
    have hline : (fun y : ℝ => G (-((-c : ℝ) + 2 * Real.pi * y * Complex.I))) = F := by
      funext y
      simp only [F]
      congr 1
      push_cast
      ring
    rw [hline]
    have hpow : (↑(Real.exp (-u)) : ℂ) ^ (↑c : ℂ) = ↑(Real.exp (-(c * u))) := by
      rw [← Complex.ofReal_cpow (le_of_lt (Real.exp_pos _)), ← Real.exp_mul]
      congr 2
      ring
    rw [Complex.ofReal_neg, neg_neg, hpow, ← smul_assoc]
    rw [Complex.real_smul, ← Complex.ofReal_mul, ← Real.exp_add]
    simp
  have hF_cont : Continuous F := by
    have h := hG_cont.comp (show Continuous (fun y : ℝ => y * -(2 * Real.pi)) by fun_prop)
    convert h using 1
    funext y
    simp only [F, Function.comp_apply]
    congr 1
    push_cast
    ring
  have hfour_int : Integrable (𝓕 F) := by
    have heq : (𝓕 F) = fun u => p (-u) := by
      funext u
      simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using (hp_eq (-u)).symm
    rw [heq]
    exact hp_int.comp_neg
  have hFF (u : ℝ) : 𝓕 p u = F u := by
    rw [funext hp_eq]
    exact hF_int.fourier_fourierInv_eq hfour_int hF_cont.continuousAt
  intro t
  rw [mellin_eq_fourier]
  have harg : (-((c : ℂ) + ↑t * Complex.I)).im / (2 * Real.pi) = -t / (2 * Real.pi) := by
    simp
  rw [harg]
  have hp_rw : (fun u : ℝ => Real.exp (-(-((c : ℂ) + ↑t * Complex.I)).re * u) •
      g (Real.exp (-u))) = p := by
    funext u
    simp only [p, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im,
      zero_mul, sub_zero, add_zero, neg_neg]
  rw [hp_rw, hFF]
  simp only [F]
  have hscale : 2 * Real.pi * (-t / (2 * Real.pi)) = -t := by
    field_simp
  rw [hscale]
  simp

end DedekindZetaZeroFree
