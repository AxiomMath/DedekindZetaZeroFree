module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

@[expose] public section

noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation

def averageCLM {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] :
    C(X, ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 μ ℂ)

theorem averageCLM_apply {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (v : C(X, ℂ)) : averageCLM μ v = ∫ x, v x ∂μ := by
  change L1.integralCLM' ℂ (ContinuousMap.toLp 1 μ ℂ v) = _
  rw [← L1.integral_eq', L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp μ v)

end DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation

end
