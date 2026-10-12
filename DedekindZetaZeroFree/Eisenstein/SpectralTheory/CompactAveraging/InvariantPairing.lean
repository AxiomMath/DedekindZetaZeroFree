module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

noncomputable section
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualAveragePairing
variable {K X : Type*} [MeasurableSpace K] [MeasurableSpace X]
variable (ν : Measure K) [IsProbabilityMeasure ν] (μ : Measure X) [SFinite μ]

theorem fixed_pairing_average
    (a : K → X → X)
    (ha : Measurable (fun p : K × X => (p.1, a p.1 p.2)))
    (hm : ∀ k, MeasurePreserving (a k) μ μ)
    (he : ∀ k, MeasurableEmbedding (a k))
    (c f : X → ℂ)
    (hI : Integrable (fun x => star (c x) * f x) μ)
    (hc : ∀ k x, c (a k x) = c x) :
    (∫ x, star (c x) * (∫ k, f (a k x) ∂ν) ∂μ) =
      ∫ x, star (c x) * f x ∂μ := by
  have hp : MeasurePreserving (fun p : K × X => (p.1, a p.1 p.2)) (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product (measurable_snd.comp ha) (Filter.Eventually.of_forall fun k => (hm k).map_eq)
  have hi : Integrable (fun p : K × X => star (c p.2) * f (a p.1 p.2)) (ν.prod μ) := by
    have hh := hp.integrable_comp_of_integrable (hI.comp_snd ν)
    simpa only [Function.comp_def, hc] using hh
  calc
    (∫ x, star (c x) * (∫ k, f (a k x) ∂ν) ∂μ) =
        ∫ x, ∫ k, star (c x) * f (a k x) ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_const_mul _ _).symm
    _ = ∫ k, ∫ x, star (c x) * f (a k x) ∂μ ∂ν := (integral_integral_swap hi).symm
    _ = ∫ k : K, (∫ x, star (c x) * f x ∂μ) ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with k
      have hh := (hm k).integral_comp (he k) (fun x => star (c x) * f x)
      simpa only [hc] using hh
    _ = _ := by simp

end DedekindZetaZeroFree.FourierContinuation.ResidualAveragePairing

end
