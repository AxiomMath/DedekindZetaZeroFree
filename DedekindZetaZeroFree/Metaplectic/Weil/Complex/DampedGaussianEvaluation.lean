module

public import DedekindZetaZeroFree.Metaplectic.Weil.Complex.QuadraticUnitaryCoordinates
public import DedekindZetaZeroFree.Metaplectic.Weil.Complex.TraceFourierNormalization

@[expose] public section

/-
The one-dimensional Gaussian integral API is imported from Mathlib's
`Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`, by Sébastien Gouëzel
(Apache 2.0).
-/

namespace DedekindZetaZeroFree.ComplexWeil

noncomputable section
open MeasureTheory

theorem gaussian_principal_prefactor (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) :
    let bMinus : ℂ := (ε : ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (r : ℂ)
    let bPlus : ℂ := (ε : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (r : ℂ)
    ((Real.pi : ℂ) / bMinus) ^ (1 / 2 : ℂ) *
        ((Real.pi : ℂ) / bPlus) ^ (1 / 2 : ℂ) =
      ((Real.pi / Real.sqrt (ε ^ 2 + 4 * Real.pi ^ 2 * r ^ 2) : ℝ) : ℂ) := by
  dsimp
  let b : ℂ := (ε : ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (r : ℂ)
  have hb : Complex.normSq b = ε ^ 2 + 4 * Real.pi ^ 2 * r ^ 2 := by
    simp [b, Complex.normSq_apply]
    ring
  have hbpos : 0 < Complex.normSq b := by
    rw [hb]
    have : 0 < ε ^ 2 := sq_pos_of_pos hε
    positivity
  have harg : ((Real.pi : ℂ) / b).arg ≠ Real.pi := by
    rw [Ne, Complex.arg_eq_pi_iff]
    have hre : 0 < ((Real.pi : ℂ) / b).re := by
      simpa [Complex.div_re, b] using div_pos (mul_pos Real.pi_pos hε) hbpos
    exact fun h => (not_lt_of_ge hre.le) h.1
  have hc : (ε : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) =
      (starRingEnd ℂ) b := by simp [b, map_ofNat]
  change ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) *
    ((Real.pi : ℂ) / ((ε : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (r : ℂ))) ^
      (1 / 2 : ℂ) = _
  rw [hc]
  have hd : (Real.pi : ℂ) / (starRingEnd ℂ) b =
      (starRingEnd ℂ) ((Real.pi : ℂ) / b) := by simp
  rw [hd, Complex.conj_cpow _ _ harg]
  have hh : (starRingEnd ℂ) (1 / 2 : ℂ) = (1 / 2 : ℂ) := by simp [map_ofNat]
  rw [hh, Complex.mul_conj']
  have he : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [he, Complex.norm_cpow_real, ← Real.sqrt_eq_rpow,
    ← Complex.ofReal_pow, Real.sq_sqrt (norm_nonneg _), norm_div,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_def, hb]

private theorem real_gaussian_eval (b : ℂ) (hb : 0 < b.re) (v : ℝ) :
    (∫ x : ℝ, Complex.exp (-b * (x : ℂ) ^ 2 +
      Complex.I * (2 * (Real.pi : ℂ) * (v : ℂ)) * (x : ℂ))) =
      ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) *
        Complex.exp (-(Real.pi : ℂ) ^ 2 * (v : ℂ) ^ 2 / b) := by
  simp_rw [Complex.exp_add]
  rw [show (fun x : ℝ => Complex.exp (-b * (x : ℂ) ^ 2) *
      Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (v : ℂ)) * (x : ℂ))) =
      (fun x : ℝ => Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (v : ℂ)) * (x : ℂ)) *
      Complex.exp (-b * (x : ℂ) ^ 2)) from by funext x; exact mul_comm _ _]
  rw [fourierIntegral_gaussian hb]
  congr 2
  have hn : b ≠ 0 := fun h => by simp [h] at hb
  field_simp
  ring

private theorem rotated_integrand (β a ξ : ℂ) (ε : ℝ) (u : ℂ) (hu : ‖u‖ = 1)
    (hrotate : β * a * u ^ 2 = (‖β * a‖ : ℂ)) (s t : ℝ) :
    Complex.exp (((-ε * ‖u * ((s : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ)) *
      psi β (a * (u * ((s : ℂ) + (t : ℂ) * Complex.I)) ^ 2 -
        (u * ((s : ℂ) + (t : ℂ) * Complex.I)) * ξ) =
    Complex.exp (-((ε : ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (‖β * a‖ : ℂ)) *
        (s : ℂ) ^ 2 + Complex.I * (2 * (Real.pi : ℂ) * (-((β * u * ξ).re : ℂ))) * (s : ℂ)) *
    Complex.exp (-((ε : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (‖β * a‖ : ℂ)) *
        (t : ℂ) ^ 2 + Complex.I * (2 * (Real.pi : ℂ) * ((β * u * ξ).im : ℂ)) * (t : ℂ)) := by
  unfold psi
  rw [← Complex.exp_add, ← Complex.exp_add, norm_sq_unit_coordinates u hu]
  congr 1
  have hquad := quadratic_re_unit_coordinates β a u hrotate s t
  have hlin := linear_re_unit_coordinates β u ξ s t
  rw [mul_sub, Complex.sub_re]
  have hq : (β * (a * (u * ((s : ℂ) + (t : ℂ) * Complex.I)) ^ 2)).re =
      ‖β * a‖ * (s ^ 2 - t ^ 2) := by simpa [mul_assoc] using hquad
  have hl : (β * (u * ((s : ℂ) + (t : ℂ) * Complex.I) * ξ)).re =
      (β * u * ξ).re * s - (β * u * ξ).im * t := by simpa [mul_assoc] using hlin
  rw [hq, hl]
  push_cast
  ring

theorem damped_gaussian_evaluation (β a ξ : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (u : ℂ) (hu : ‖u‖ = 1)
    (hrotate : β * a * u ^ 2 = (‖β * a‖ : ℂ)) :
    let r : ℝ := ‖β * a‖
    let p : ℝ := (β * u * ξ).re
    let q : ℝ := (β * u * ξ).im
    let bMinus : ℂ := (ε : ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (r : ℂ)
    let bPlus : ℂ := (ε : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (r : ℂ)
    K β ε a ξ =
      ((‖β‖ * Real.pi / Real.sqrt (ε ^ 2 + 4 * Real.pi ^ 2 * r ^ 2) : ℝ) : ℂ) *
        Complex.exp (-(Real.pi : ℂ) ^ 2 * (p : ℂ) ^ 2 / bMinus -
          (Real.pi : ℂ) ^ 2 * (q : ℂ) ^ 2 / bPlus) := by
  dsimp
  let bm : ℂ := (ε : ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (‖β * a‖ : ℂ)
  let bp : ℂ := (ε : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (‖β * a‖ : ℂ)
  have hm : 0 < bm.re := by simpa [bm] using hε
  have hp : 0 < bp.re := by simpa [bp] using hε
  let f : ℂ → ℂ := fun x => Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) *
    psi β (a * x ^ 2 - x * ξ)
  have hrot : (∫ x : ℂ, f x) = ∫ x : ℂ, f (u * x) := by
    symm
    exact (unitMulCLE_measurePreserving u hu).integral_comp
      (unitMulCLE u hu).toHomeomorph.measurableEmbedding f
  have hcoords : (∫ x : ℂ, f (u * x)) =
      ∫ x : ℝ × ℝ, f (u * ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I)) := by
    symm
    convert (Complex.volume_preserving_equiv_real_prod.symm
      Complex.measurableEquivRealProd).integral_comp
      Complex.measurableEquivRealProd.symm.measurableEmbedding (fun x => f (u * x)) using 1
    congr 1
    funext x
    congr 2
    apply Complex.ext <;> simp
  unfold K mu
  rw [integral_smul_measure, ENNReal.toReal_ofReal (norm_nonneg β)]
  change (‖β‖ : ℂ) * (∫ x : ℂ, f x) = _
  rw [hrot, hcoords]
  have hsplit : (fun x : ℝ × ℝ => f (u * ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I))) =
      fun x : ℝ × ℝ =>
        Complex.exp (-bm * (x.1 : ℂ) ^ 2 + Complex.I *
          (2 * (Real.pi : ℂ) * (-((β * u * ξ).re : ℂ))) * (x.1 : ℂ)) *
        Complex.exp (-bp * (x.2 : ℂ) ^ 2 + Complex.I *
          (2 * (Real.pi : ℂ) * ((β * u * ξ).im : ℂ)) * (x.2 : ℂ)) := by
    funext x
    exact rotated_integrand β a ξ ε u hu hrotate x.1 x.2
  rw [hsplit, Measure.volume_eq_prod]
  rw [integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := fun s : ℝ => Complex.exp (-bm * (s : ℂ) ^ 2 +
      Complex.I * (2 * (Real.pi : ℂ) * (-((β * u * ξ).re : ℂ))) * (s : ℂ)))
    (g := fun t : ℝ => Complex.exp (-bp * (t : ℂ) ^ 2 +
      Complex.I * (2 * (Real.pi : ℂ) * ((β * u * ξ).im : ℂ)) * (t : ℂ)))]
  have hgm := real_gaussian_eval bm hm (- (β * u * ξ).re)
  simp only [Complex.ofReal_neg, neg_sq] at hgm
  rw [hgm, real_gaussian_eval bp hp (β * u * ξ).im]
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  have hpre := gaussian_principal_prefactor ε ‖β * a‖ hε
    (quadratic_radius_pos β a hβ ha)
  dsimp at hpre
  rw [hpre]
  dsimp [bm, bp]
  push_cast
  ring

end
end DedekindZetaZeroFree.ComplexWeil
