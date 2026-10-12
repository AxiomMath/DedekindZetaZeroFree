module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree.Audit.Euler

noncomputable section

def principalFactor (r D E : ℂ) : ℂ :=
  (1 + r) / (1 - r) + (1 + r) * (E - D) / (1 - E)

def principalCorrection (r D E : ℂ) : ℂ :=
  (1 - r ^ 2) * (1 - (1 - r) * D - r * E) / ((1 - E) * (1 - D))

theorem principalCorrection_identity (r D E : ℂ) (hr : 1 - r ≠ 0)
    (hD : 1 - D ≠ 0) (hE : 1 - E ≠ 0) :
    (1 - r) ^ 2 * principalFactor r D E / (1 - D) = principalCorrection r D E := by
  unfold principalFactor principalCorrection
  field_simp
  <;> ring

theorem principalCorrection_numerator_subtraction (r D E : ℂ) :
    (1 - r ^ 2) * (1 - (1 - r) * D - r * E) - (1 - E) * (1 - D) =
      -r ^ 2 + (r + r ^ 2 - r ^ 3) * D + (1 - r + r ^ 3) * E - E * D := by
  ring

theorem principalCorrection_ne_zero (r : ℝ) (D E : ℂ)
    (hr0 : 0 < r) (hr1 : r < 1) (hD : ‖D‖ < 1) (hE : ‖E‖ < 1) :
    principalCorrection (r : ℂ) D E ≠ 0 := by
  have hweight : ‖(1 - (r : ℂ)) * D + (r : ℂ) * E‖ < 1 := by
    calc
      ‖(1 - (r : ℂ)) * D + (r : ℂ) * E‖ ≤
          ‖(1 - (r : ℂ)) * D‖ + ‖(r : ℂ) * E‖ := norm_add_le _ _
      _ = (1 - r) * ‖D‖ + r * ‖E‖ := by
        have hcast : (1 : ℂ) - (r : ℂ) = ((1 - r : ℝ) : ℂ) := by push_cast; ring
        rw [norm_mul, norm_mul, hcast]
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr hr1.le), abs_of_nonneg hr0.le]
      _ < (1 - r) * 1 + r * 1 :=
        add_lt_add (mul_lt_mul_of_pos_left hD (sub_pos.mpr hr1))
          (mul_lt_mul_of_pos_left hE hr0)
      _ = 1 := by ring
  have hnum : 1 - (1 - (r : ℂ)) * D - (r : ℂ) * E ≠ 0 := by
    intro hz
    have heq : (1 - (r : ℂ)) * D + (r : ℂ) * E = 1 := by
      linear_combination -hz
    rw [heq, norm_one] at hweight
    exact (lt_irrefl 1) hweight
  have hDne : 1 - D ≠ 0 := by
    intro hz
    have : D = 1 := (sub_eq_zero.mp hz).symm
    simp [this] at hD
  have hEne : 1 - E ≠ 0 := by
    intro hz
    have : E = 1 := (sub_eq_zero.mp hz).symm
    simp [this] at hE
  have hn : 1 - r ^ 2 ≠ 0 := by nlinarith [sq_nonneg r]
  unfold principalCorrection
  exact div_ne_zero (mul_ne_zero (by exact_mod_cast hn) hnum) (mul_ne_zero hEne hDne)

end
end DedekindZetaZeroFree.Audit.Euler
