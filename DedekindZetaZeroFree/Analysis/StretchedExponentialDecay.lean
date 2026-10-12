module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

namespace DedekindZetaZeroFree

theorem thetaStretchedExponentialPower (p B : ℝ) (hp : 0 < p) (hB : 0 < B)
    (r : ℝ) :
    Asymptotics.IsLittleO Filter.atTop
      (fun t : ℝ => Real.exp (-B * Real.rpow t p))
      (fun t : ℝ => Real.rpow t r) := by
  have h1 : Asymptotics.IsLittleO Filter.atTop
      (fun x : ℝ => Real.exp (-B * x)) (fun x : ℝ => Real.rpow x (r / p)) :=
    isLittleO_exp_neg_mul_rpow_atTop hB (r / p)
  have h2 : Asymptotics.IsLittleO Filter.atTop
      (fun t : ℝ => Real.exp (-B * Real.rpow t p))
      (fun t : ℝ => Real.rpow (Real.rpow t p) (r / p)) :=
    h1.comp_tendsto (tendsto_rpow_atTop hp)
  refine h2.congr' (Filter.EventuallyEq.refl _ _) ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul ht p (r / p), mul_comm p (r / p), div_mul_cancel₀ r hp.ne']

theorem thetaStretchedExponentialPower_bound (p B : ℝ) (hp : 0 < p) (hB : 0 < B)
    (F : ℝ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hF : ∀ t : ℝ, 1 ≤ t → ‖F t‖ ≤ A * Real.exp (-B * Real.rpow t p)) :
    ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop F (fun t : ℝ => Real.rpow t r) := by
  intro r
  have hbig : Asymptotics.IsBigO Filter.atTop F
      (fun t : ℝ => A * Real.exp (-B * Real.rpow t p)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    rw [one_mul, norm_mul, Real.norm_of_nonneg hA,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hF t ht
  have hlit : Asymptotics.IsLittleO Filter.atTop
      (fun t : ℝ => A * Real.exp (-B * Real.rpow t p))
      (fun t : ℝ => Real.rpow t r) :=
    (thetaStretchedExponentialPower p B hp hB r).const_mul_left A
  exact hbig.trans hlit.isBigO

end DedekindZetaZeroFree
