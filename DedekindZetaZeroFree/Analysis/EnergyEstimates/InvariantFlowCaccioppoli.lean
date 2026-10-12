module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped Topology BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.Caccioppoli
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

 theorem cutoff_young (χ dχ : ℝ) (u du : ℂ) :
    |2 * χ * dχ * (star u * du).re| ≤
      (χ ^ 2 * ‖du‖ ^ 2) / 2 + 2 * dχ ^ 2 * ‖u‖ ^ 2 := by
  have hp : |(star u * du).re| ≤ ‖u‖ * ‖du‖ := by
    exact (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, norm_star])
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (2 * χ * dχ))
  have hs := sq_nonneg (|χ| * ‖du‖ - 2 * |dχ| * ‖u‖)
  simp only [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)] at hm ⊢
  nlinarith [sq_abs χ, sq_abs dχ]

 theorem finite_energy_of_cutoff_bound
    (e : X → ℝ) (he : Measurable e) (he0 : ∀ x, 0 ≤ e x)
    (χ : ℕ → X → ℝ) (hχ : ∀ n, Measurable (χ n))
    (hχlim : ∀ x, Filter.Tendsto (fun n => χ n x) Filter.atTop (𝓝 1))
    (hi : ∀ n, Integrable (fun x => χ n x ^ 2 * e x) μ)
    (M : ℝ) (hM : ∀ n, (∫ x, χ n x ^ 2 * e x ∂μ) ≤ M) :
    (∫⁻ x, ENNReal.ofReal (e x) ∂μ) < ⊤ := by
  have hlim (x : X) : Filter.Tendsto
      (fun n => ENNReal.ofReal (χ n x ^ 2 * e x)) Filter.atTop
      (𝓝 (ENNReal.ofReal (e x))) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((hχlim x).pow 2).mul_const (e x))
    simp only [one_pow, one_mul] at hh
    change Filter.Tendsto (fun n => ENNReal.ofReal (χ n x ^ 2 * e x))
      Filter.atTop (𝓝 (ENNReal.ofReal (e x))) at hh
    exact hh
  calc
    _ = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (χ n x ^ 2 * e x)) Filter.atTop ∂μ := by
      apply lintegral_congr
      intro x
      exact (hlim x).liminf_eq.symm
    _ ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (χ n x ^ 2 * e x) ∂μ) Filter.atTop :=
      lintegral_liminf_le (fun n => ENNReal.measurable_ofReal.comp (((hχ n).pow_const 2).mul he))
    _ ≤ ENNReal.ofReal M := by
      apply Filter.liminf_le_of_frequently_le'
      apply Filter.Eventually.frequently
      apply Filter.Eventually.of_forall
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (hi n)
        (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (he0 x)))]
      exact ENNReal.ofReal_le_ofReal (hM n)
    _ < ⊤ := ENNReal.ofReal_lt_top

end DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.Caccioppoli

end
