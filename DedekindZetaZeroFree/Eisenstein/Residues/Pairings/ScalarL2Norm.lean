module

public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace DedekindZetaZeroFree.FourierContinuation.ResidualScalarNorm
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
theorem pairing_self_eq_lpNorm_sq (f : X → ℂ) (hf : MemLp f 2 μ) :
    (∫x, star (f x)*f x ∂μ) = ((lpNorm f 2 μ)^2 : ℝ) := by
  have he : (∫x, star (f x)*f x ∂μ) = inner ℂ (hf.toLp f) (hf.toLp f) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    change star (f x)*f x = (hf.toLp f) x * star ((hf.toLp f) x)
    rw [hx]
    exact mul_comm _ _
  rw [he, inner_self_eq_norm_sq_to_K, Lp.norm_toLp]
  simp only [lpNorm]
  norm_cast

theorem norm_pairing_self (f : X → ℂ) (hf : MemLp f 2 μ) :
    ‖∫x, star (f x)*f x ∂μ‖ = (lpNorm f 2 μ)^2 := by
  rw [pairing_self_eq_lpNorm_sq f hf]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (lpNorm f 2 μ))]

theorem lpNorm_le_of_pairing_bound (f : X → ℂ) (hf : MemLp f 2 μ)
    (B p : ℝ) (hB : 0 ≤ B) (hp : 0 ≤ p)
    (h : ‖∫x, star (f x)*f x ∂μ‖ ≤ B*p^2) :
    lpNorm f 2 μ ≤ Real.sqrt B*p := by
  rw [norm_pairing_self f hf] at h
  have hs := Real.sq_sqrt hB
  have hl : 0 ≤ lpNorm f 2 μ := ENNReal.toReal_nonneg
  have hr : 0 ≤ Real.sqrt B*p := mul_nonneg (Real.sqrt_nonneg B) hp
  have he : (Real.sqrt B*p)^2 = B*p^2 := by rw [mul_pow, hs]
  nlinarith

end DedekindZetaZeroFree.FourierContinuation.ResidualScalarNorm

end
