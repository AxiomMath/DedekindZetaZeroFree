module

public import DedekindZetaZeroFree.Analysis.CauchyCenterContinuity

@[expose] public section

noncomputable section
open scoped Topology NNReal
open Complex Filter
namespace DedekindZetaZeroFree.EisensteinSmoothGerms
open ComplexAnalysis.KernelTaylor.CauchyOperators
variable {X : Type*} [TopologicalSpace X]

theorem scalar_cauchy_coefficients_radius_independent
    (f : ℂ → ℂ) (ρ : ℝ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 ρ))
    (t u : ℝ) (ht : 0 < t) (hu : 0 < u) (htρ : t < ρ) (huρ : u < ρ)
    (n : ℕ) : (cauchyPowerSeries f 0 t).coeff n =
      (cauchyPowerSeries f 0 u).coeff n := by
  have hpt := (hf.differentiableOn.mono
    (Metric.closedBall_subset_ball htρ)).hasFPowerSeriesOnBall
      (R := ⟨t, ht.le⟩) ht
  have hpu := (hf.differentiableOn.mono
    (Metric.closedBall_subset_ball huρ)).hasFPowerSeriesOnBall
      (R := ⟨u, hu.le⟩) hu
  have he := hpt.hasFPowerSeriesAt.eq_formalMultilinearSeries hpu.hasFPowerSeriesAt
  exact congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) he

end DedekindZetaZeroFree.EisensteinSmoothGerms

end
