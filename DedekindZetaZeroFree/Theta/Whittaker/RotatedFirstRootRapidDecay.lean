module

public import DedekindZetaZeroFree.Analysis.Complex.LogarithmicRadialDerivatives
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ComplexExceptionalFunctional

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCplxRotatedJacquetIntegralBounds

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxRotatedKernelEstimates MeasureTheory

instance instIsAddHaarMeasureRotatedKernelEuclideanArea : euclideanArea.IsAddHaarMeasure := by unfold euclideanArea; infer_instance

end DedekindZetaZeroFree.KPCplxRotatedJacquetIntegralBounds

end

section

namespace DedekindZetaZeroFree.KPCplxRotatedRapidDecay

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
  KPCplxJacquetFunctional KPCplxRotatedKernelEstimates

open MeasureTheory

open scoped ContDiff Matrix.Norms.Elementwise

theorem radial_min_bound_of_power_bounds {ι : Type*} (F : ι → ℂˣ → ℂ)
    (A : ℝ) (hA : 0 < A)
    (hb : ∀ h : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i y,
      ‖F i y‖ ≤ C * ‖(y : ℂ)‖ ^ ((2 / 3 : ℝ) - (h : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i y,
      ‖F i y‖ ≤ C * min ((complexAbs (y : ℂ)) ^ (1 / 3 : ℝ))
        ((complexAbs (y : ℂ)) ^ (-A)) := by
  obtain ⟨h, hh⟩ := exists_nat_ge (2 * A + (2 / 3 : ℝ))
  obtain ⟨C₀, hC₀, hb₀⟩ := hb 0
  obtain ⟨C₁, hC₁, hb₁⟩ := hb h
  refine ⟨max C₀ C₁, le_trans hC₀ (le_max_left _ _), ?_⟩
  intro i y
  have hr : 0 < ‖(y : ℂ)‖ := norm_pos_iff.mpr y.ne_zero
  have he (a : ℝ) : (complexAbs (y : ℂ)) ^ a = ‖(y : ℂ)‖ ^ (2 * a) := by
    rw [complexAbs, ← Real.rpow_natCast_mul hr.le]
    rfl
  rw [he, he]
  norm_num only [show (2 : ℝ) * (1 / 3) = 2 / 3 by norm_num,
    show (2 : ℝ) * -A = -2 * A by ring]
  rw [mul_min_of_nonneg _ _ (le_trans hC₀ (le_max_left _ _))]
  apply le_min
  · have hz := hb₀ i y
    simp only [Nat.cast_zero, sub_zero] at hz
    exact hz.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le _))
  · by_cases hr₁ : ‖(y : ℂ)‖ ≤ 1
    · have hz := hb₀ i y
      simp only [Nat.cast_zero, sub_zero] at hz
      have hp : ‖(y : ℂ)‖ ^ (2 / 3 : ℝ) ≤ ‖(y : ℂ)‖ ^ (-2 * A) :=
        Real.rpow_le_rpow_of_exponent_ge hr hr₁ (by linarith)
      exact hz.trans ((mul_le_mul_of_nonneg_left hp hC₀).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le _)))
    · have hp : ‖(y : ℂ)‖ ^ ((2 / 3 : ℝ) - (h : ℝ)) ≤ ‖(y : ℂ)‖ ^ (-2 * A) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hr₁)) (by linarith)
      exact (hb₁ i y).trans ((mul_le_mul_of_nonneg_left hp hC₁).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr.le _)))

end DedekindZetaZeroFree.KPCplxRotatedRapidDecay

end
