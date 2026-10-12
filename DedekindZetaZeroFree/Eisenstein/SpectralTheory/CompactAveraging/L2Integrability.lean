module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

noncomputable section
open scoped Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualAverageL2
variable {K X : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology K] [SecondCountableTopology X]
variable (ν : Measure K) [IsProbabilityMeasure ν] (μ : Measure X) [SFinite μ]

theorem average_memLp (a : K → X → X)
    (ha : Continuous (fun p : K × X => a p.1 p.2))
    (hm : ∀ k, MeasurePreserving (a k) μ μ)
    (he : ∀ k, MeasurableEmbedding (a k))
    (f : X → ℂ) (hf : Continuous f) (h2 : MemLp f 2 μ) :
    MemLp (fun x => ∫ k, f (a k x) ∂ν) 2 μ := by
  have hc : Continuous (fun p : K × X => f (a p.1 p.2)) := hf.comp ha
  have hsq : Integrable (fun p : K × X => ‖f (a p.1 p.2)‖ ^ 2) (ν.prod μ) := by
    apply (integrable_prod_iff ((hc.norm.pow 2).aestronglyMeasurable)).mpr
    constructor
    · exact Filter.Eventually.of_forall fun k =>
        (memLp_two_iff_integrable_sq_norm ((h2.comp_measurePreserving (hm k)).aestronglyMeasurable)).mp
          (h2.comp_measurePreserving (hm k))
    · have he : (fun k => ∫ x, ‖‖f (a k x)‖ ^ 2‖ ∂μ) =
          fun _ : K => ∫ x, ‖f x‖ ^ 2 ∂μ := by
        funext k
        simp only [norm_pow, norm_norm]
        exact (hm k).integral_comp (he k) (fun x => ‖f x‖ ^ 2)
      simp only [Pi.pow_apply]
      rw [he]
      exact integrable_const _
  have havg : Continuous (fun x => ∫ k, f (a k x) ∂ν) := by
    rw [← continuousOn_univ]
    exact continuousOn_integral_of_compact_support (μ := ν) isCompact_univ
      (hc.comp continuous_swap).continuousOn (fun _ _ _ hk => (hk (Set.mem_univ _)).elim)
  apply (memLp_two_iff_integrable_sq_norm havg.aestronglyMeasurable).mpr
  apply hsq.integral_prod_right.mono' (havg.norm.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hcx : Continuous (fun k => f (a k x)) := hc.comp (continuous_id.prodMk continuous_const)
    exact ((convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set ℂ))).pow
      (fun _ _ => norm_nonneg _) 2).map_integral_le
      (continuous_norm.pow 2).continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
      (hcx.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((hcx.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
end DedekindZetaZeroFree.FourierContinuation.ResidualAverageL2

end
