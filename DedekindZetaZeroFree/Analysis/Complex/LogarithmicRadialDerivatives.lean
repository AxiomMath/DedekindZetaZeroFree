module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

import Mathlib.Analysis.Calculus.Deriv.Shift

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxRotatedRapidDecay

noncomputable def logarithmicRadialFlow (t : ℝ) (y : ℂˣ) : ℂˣ :=
  Units.mk0 ((Real.exp (t / 2) : ℂ) * (y : ℂ)) (by
    exact mul_ne_zero (by exact_mod_cast Real.exp_ne_zero (t / 2)) y.ne_zero)

noncomputable def logarithmicDerivative (F : ℂˣ → ℂ) : ℂˣ → ℂ :=
  fun y => deriv (fun t : ℝ => F (logarithmicRadialFlow t y)) 0

lemma logarithmicRadialFlow_add (s t : ℝ) (z : ℂˣ) :
    logarithmicRadialFlow s (logarithmicRadialFlow t z) =
      logarithmicRadialFlow (s + t) z := by
  apply Units.ext
  simp only [logarithmicRadialFlow, Units.val_mk0]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

@[simp] lemma logarithmicRadialFlow_zero (z : ℂˣ) : logarithmicRadialFlow 0 z = z := by
  apply Units.ext
  simp [logarithmicRadialFlow]

lemma iteratedDeriv_logarithmicRadialFlow (f : ℂˣ → ℂ) (j : ℕ) (z : ℂˣ) (t : ℝ) :
    iteratedDeriv j (fun s => f (logarithmicRadialFlow s z)) t =
      ((logarithmicDerivative^[j]) f) (logarithmicRadialFlow t z) := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, Function.iterate_succ_apply', logarithmicDerivative]
    have hfun : (fun s => ((logarithmicDerivative^[j]) f) (logarithmicRadialFlow s z)) =
        iteratedDeriv j (fun s => f (logarithmicRadialFlow s z)) := by
      funext s
      exact (ih s).symm
    simp_rw [logarithmicRadialFlow_add]
    rw [deriv_comp_add_const
      (fun s => ((logarithmicDerivative^[j]) f) (logarithmicRadialFlow s z)) t 0]
    simp only [zero_add]
    rw [hfun]

lemma iteratedDeriv_scale (g : ℝ → ℂ) (c : ℝ) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun s => g (c * s)) t =
      (c : ℂ) ^ j * iteratedDeriv j g (c * t) := by
  induction j generalizing t with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ j ih =>
    have he : iteratedDeriv j (fun s => g (c * s)) =
        fun s => (c : ℂ) ^ j * iteratedDeriv j g (c * s) := funext ih
    rw [iteratedDeriv_succ, he, deriv_const_mul_field]
    rw [deriv_comp_mul_left c (iteratedDeriv j g) t]
    rw [iteratedDeriv_succ]
    change (c : ℂ) ^ j * ((c : ℂ) * deriv (iteratedDeriv j g) (c * t)) = _
    ring

lemma iteratedDeriv_logarithmicRadialFlow_div (f : ℂˣ → ℂ) (r : ℝ) (j : ℕ) (z : ℂˣ) :
    iteratedDeriv j (fun t => f (logarithmicRadialFlow (t / r) z)) 0 =
      (r⁻¹ : ℂ) ^ j * ((logarithmicDerivative^[j]) f) z := by
  have hfun : (fun t => f (logarithmicRadialFlow (t / r) z)) =
      fun t => (fun s => f (logarithmicRadialFlow s z)) (r⁻¹ * t) := by
    funext t
    rw [div_eq_mul_inv, mul_comm t]
  rw [hfun]
  have h := iteratedDeriv_scale (fun s => f (logarithmicRadialFlow s z)) r⁻¹ j 0
  simpa only [mul_zero, iteratedDeriv_logarithmicRadialFlow, logarithmicRadialFlow_zero,
    Complex.ofReal_inv] using h

end DedekindZetaZeroFree.KPCplxRotatedRapidDecay
