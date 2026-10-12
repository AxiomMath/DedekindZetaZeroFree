module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace DedekindZetaZeroFree.KPContinuation

noncomputable section

def spectralDomain : Set ℂ := {s | -(1 : ℝ) / 6 < s.re}

theorem spectralDomain_isOpen : IsOpen spectralDomain := by
  exact isOpen_lt continuous_const Complex.continuous_re

theorem spectralDomain_isConnected : IsConnected spectralDomain := by
  apply (convex_halfSpace_gt (f := Complex.re)
    ⟨fun x y => by simp, fun a x => by simp⟩ (-(1 : ℝ) / 6)).isConnected
  exact ⟨0, by norm_num [spectralDomain]⟩

theorem convergenceHalfPlane_subset_spectralDomain :
    {s : ℂ | (1 : ℝ) / 3 < s.re} ⊆ spectralDomain := by
  intro s hs
  dsimp [spectralDomain] at *
  linarith

theorem exceptionalBall_subset_spectralDomain :
    Metric.ball (0 : ℂ) ((1 : ℝ) / 6) ⊆ spectralDomain := by
  intro s hs
  have hn : ‖s‖ < (1 : ℝ) / 6 := by simpa using hs
  have hr := Complex.abs_re_le_norm s
  dsimp [spectralDomain]
  have h := neg_lt_of_abs_lt (lt_of_le_of_lt hr hn)
  linarith

end
end DedekindZetaZeroFree.KPContinuation

section

namespace DedekindZetaZeroFree.KPContinuation

noncomputable section

def spectralCoordinate (d : ℤ) (s : ℂ) : ℂ :=
  (d : ℂ) * (1 - ((1 : ℂ) / 3 + 2 * s) ^ 2)

def thresholdRay (d : ℤ) : Set ℂ := {μ | μ.im = 0 ∧ (d : ℝ) ≤ μ.re}

theorem spectralCoordinate_avoids_thresholdRay (d : ℤ) (hd : 0 < d) :
    spectralCoordinate d '' spectralDomain ⊆ (thresholdRay d)ᶜ := by
  rintro _ ⟨s, hs, rfl⟩ hμ
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let u : ℂ := (1 : ℂ) / 3 + 2 * s
  have hu : 0 < u.re := by
    dsimp [u]
    norm_num
    have hs' : -(1 : ℝ) / 6 < s.re := hs
    linarith
  change ((d : ℂ) * (1 - u ^ 2)).im = 0 ∧
    (d : ℝ) ≤ ((d : ℂ) * (1 - u ^ 2)).re at hμ
  have hi : (d : ℝ) * (-(2 * u.re * u.im)) = 0 := by
    have h := hμ.1
    simp only [pow_two, Complex.mul_im, Complex.mul_re, Complex.sub_im,
      Complex.sub_re, Complex.one_im, Complex.one_re, Complex.intCast_re,
      Complex.intCast_im, zero_mul, zero_add, mul_zero, add_zero] at h
    nlinarith [h]
  have hui : u.im = 0 := by
    have hz := (mul_eq_zero.mp hi).resolve_left (ne_of_gt hdR)
    have hz' : u.re * u.im = 0 := by linarith
    exact (mul_eq_zero.mp hz').resolve_left (ne_of_gt hu)
  have hr : (d : ℝ) ≤ (d : ℝ) * (1 - u.re ^ 2) := by
    have h := hμ.2
    simpa only [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.one_re, Complex.intCast_re, Complex.intCast_im, hui,
      zero_mul, mul_zero, sub_zero] using h
  nlinarith [mul_pos hdR (sq_pos_of_pos hu)]

theorem spectralCoordinate_zero (d : ℤ) :
    spectralCoordinate d 0 = 8 * (d : ℂ) / 9 := by
  unfold spectralCoordinate
  ring

theorem spectralCoordinate_hasDerivAt (d : ℤ) (s : ℂ) :
    HasDerivAt (spectralCoordinate d) (-4 * (d : ℂ) * ((1 : ℂ) / 3 + 2 * s)) s := by
  unfold spectralCoordinate
  have h := ((hasDerivAt_id s).const_mul (2 : ℂ)).const_add ((1 : ℂ) / 3)
  convert ((h.pow 2).const_sub (1 : ℂ)).const_mul (d : ℂ) using 1
  · ext z
    simp
  · simp only [id_eq, Nat.cast_ofNat, pow_one, mul_one]
    ring

theorem spectralCoordinate_deriv_zero (d : ℤ) (hd : 0 < d) :
    deriv (spectralCoordinate d) 0 = -4 * (d : ℂ) / 3 ∧
      deriv (spectralCoordinate d) 0 ≠ 0 := by
  have he : deriv (spectralCoordinate d) 0 = -4 * (d : ℂ) / 3 := by
    rw [(spectralCoordinate_hasDerivAt d 0).deriv]
    ring
  refine ⟨he, ?_⟩
  rw [he]
  exact div_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast ne_of_gt hd)) (by norm_num)

theorem spectralCoordinate_deriv_ne_zero (d : ℤ) (hd : 0 < d)
    (s : ℂ) (hs : s ∈ spectralDomain) :
    deriv (spectralCoordinate d) s ≠ 0 := by
  rw [(spectralCoordinate_hasDerivAt d s).deriv]
  apply mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast ne_of_gt hd))
  intro hz
  have hr := congrArg Complex.re hz
  norm_num at hr
  have hs' : -(1 : ℝ) / 6 < s.re := hs
  linarith

end
end DedekindZetaZeroFree.KPContinuation

end
