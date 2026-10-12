module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree.ComplexWeil

noncomputable section
open MeasureTheory

def unitMulCLE (u : ℂ) (hu : ‖u‖ = 1) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 u (norm_ne_zero_iff.mp (by rw [hu]; norm_num)))

theorem unitMulCLE_apply (u : ℂ) (hu : ‖u‖ = 1) (z : ℂ) :
    unitMulCLE u hu z = u * z := rfl

theorem quadratic_radius_pos (β a : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0) :
    0 < ‖β * a‖ := by
  exact norm_pos_iff.mpr (mul_ne_zero hβ ha)

theorem exists_quadratic_unit (β a : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ β * a * u ^ 2 = (‖β * a‖ : ℂ) := by
  have hba : β * a ≠ 0 := mul_ne_zero hβ ha
  have hr : 0 < ‖β * a‖ := norm_pos_iff.mpr hba

  set d := (‖β * a‖ : ℂ) / (β * a) with hdd
  have hdnorm : ‖d‖ = 1 := by
    rw [hdd, norm_div]
    have h1 : ‖((‖β * a‖ : ℝ) : ℂ)‖ = ‖β * a‖ := by simp
    rw [h1, div_self (norm_ne_zero_iff.mpr hba)]
  have hdexp : Complex.exp (d.arg * Complex.I) = d := by
    simpa [hdnorm] using Complex.norm_mul_exp_arg_mul_I d
  refine ⟨Complex.exp ((d.arg / 2 : ℝ) * Complex.I), ?_, ?_⟩
  · exact Complex.norm_exp_ofReal_mul_I _
  · have hsq : Complex.exp ((d.arg / 2 : ℝ) * Complex.I) ^ 2 = d := by
      rw [sq, ← Complex.exp_add]
      have : (↑(d.arg / 2) : ℂ) * Complex.I + (↑(d.arg / 2) : ℂ) * Complex.I
          = d.arg * Complex.I := by push_cast; ring
      rw [this, hdexp]
    rw [hsq, hdd]
    field_simp

theorem unitMulCLE_measurePreserving (u : ℂ) (hu : ‖u‖ = 1) :
    MeasurePreserving (unitMulCLE u hu) (volume : Measure ℂ) volume := by

  have hfun : (unitMulCLE u hu : ℂ → ℂ) = fun z : ℂ => u * z := by
    funext z; rw [unitMulCLE_apply]
  rw [hfun]
  let c : Circle := ⟨u, by
    show u ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    exact hu⟩
  have hrot : (fun z : ℂ => u * z) = (rotation c : ℂ → ℂ) := by
    funext z
    rw [rotation_apply]
  rw [hrot]
  exact LinearIsometryEquiv.measurePreserving _

theorem quadratic_re_unit_coordinates (β a u : ℂ)
    (hrotate : β * a * u ^ 2 = (‖β * a‖ : ℂ)) (s t : ℝ) :
    (β * a * (u * ((s : ℂ) + (t : ℂ) * Complex.I)) ^ 2).re =
      ‖β * a‖ * (s ^ 2 - t ^ 2) := by
  have key : β * a * (u * ((s : ℂ) + (t : ℂ) * Complex.I)) ^ 2
      = (‖β * a‖ : ℂ) * ((s : ℂ) + (t : ℂ) * Complex.I) ^ 2 := by
    rw [mul_pow]
    linear_combination ((s : ℂ) + (t : ℂ) * Complex.I) ^ 2 * hrotate
  rw [key, Complex.re_ofReal_mul, sq, Complex.mul_re]
  have hXre : ((s : ℂ) + (t : ℂ) * Complex.I).re = s := by simp
  have hXim : ((s : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  rw [hXre, hXim]
  ring

theorem linear_re_unit_coordinates (β u ξ : ℂ) (s t : ℝ) :
    (β * u * ((s : ℂ) + (t : ℂ) * Complex.I) * ξ).re =
      (β * u * ξ).re * s - (β * u * ξ).im * t := by
  have : β * u * ((s : ℂ) + (t : ℂ) * Complex.I) * ξ
      = (β * u * ξ) * ((s : ℂ) + (t : ℂ) * Complex.I) := by ring
  rw [this, Complex.mul_re]
  have hXre : ((s : ℂ) + (t : ℂ) * Complex.I).re = s := by simp
  have hXim : ((s : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  rw [hXre, hXim]

theorem norm_sq_unit_coordinates (u : ℂ) (hu : ‖u‖ = 1) (s t : ℝ) :
    ‖u * ((s : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = s ^ 2 + t ^ 2 := by
  rw [norm_mul, mul_pow, hu, one_pow, one_mul]
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem frequency_square_difference (β a u ξ : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0)
    (hrotate : β * a * u ^ 2 = (‖β * a‖ : ℂ)) :
    ((β * u * ξ).re ^ 2 - (β * u * ξ).im ^ 2) / ‖β * a‖ =
      (β * ξ ^ 2 / a).re := by
  have hba : β * a ≠ 0 := mul_ne_zero hβ ha
  have hrne : (‖β * a‖) ≠ 0 := norm_ne_zero_iff.mpr hba

  have key : (β * u * ξ) ^ 2 = (‖β * a‖ : ℂ) * (β * ξ ^ 2 / a) := by
    have h : (β * u * ξ) ^ 2 * a = (‖β * a‖ : ℂ) * (β * ξ ^ 2) := by
      rw [mul_pow]
      linear_combination (β * ξ ^ 2) * hrotate
    field_simp at h ⊢
    linear_combination h
  have hre := congrArg Complex.re key
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
  rw [sq, Complex.mul_re] at hre
  have hsq2 : (β * u * ξ).re ^ 2 - (β * u * ξ).im ^ 2
      = ‖β * a‖ * (β * ξ ^ 2 / a).re := by
    rw [sq, sq]; exact hre
  rw [hsq2]
  field_simp

end
end DedekindZetaZeroFree.ComplexWeil
