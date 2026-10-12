module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

noncomputable section
open MeasureTheory Set
namespace DedekindZetaZeroFree.FourierContinuation.ResidualGlobalFlowIBP
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] {μ : Measure X} [SigmaFinite μ]

theorem integral_stationary_derivative_zero
    (a : ℝ → X ≃ₜ X) (ha : Continuous (Function.uncurry (fun t x => a t x)))
    (ha0 : ∀ x, a 0 x = x) (hμ : ∀ t, MeasurePreserving (a t) μ μ)
    (f df : X → ℂ) (hdf : Continuous df) (hfI : Integrable f μ)
    (hdfI : Integrable df μ)
    (hderiv : ∀ t x, HasDerivAt (fun s => f (a s x)) (df (a t x)) t) :
    (∫ x, df x ∂μ) = 0 := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 1)
  have hpres : MeasurePreserving (fun p : ℝ × X => (p.1, a p.1 p.2))
      (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product ha.measurable
      (Filter.Eventually.of_forall fun t => (hμ t).map_eq)
  have hj : Integrable (fun p : ℝ × X => df (a p.1 p.2)) (ν.prod μ) :=
    hpres.integrable_comp_of_integrable (hdfI.comp_snd ν)
  have hpoint (x : X) : (∫ t in Ioc (0 : ℝ) 1, df (a t x)) = f (a 1 x) - f x := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hcont : Continuous (fun t : ℝ => df (a t x)) :=
      hdf.comp (ha.comp (continuous_id.prodMk continuous_const))
    simpa only [ha0] using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv t x) (hcont.intervalIntegrable 0 1)
  have hint : (∫ t in Ioc (0 : ℝ) 1, ∫ x, df (a t x) ∂μ) = 0 := by
    rw [integral_integral_swap hj]
    simp_rw [hpoint]
    change (∫ x, (f ∘ a 1) x - f x ∂μ) = 0
    rw [integral_sub ((hμ 1).integrable_comp_of_integrable hfI) hfI]
    exact sub_eq_zero.mpr ((hμ 1).integral_comp (a 1).measurableEmbedding f)
  have heq (t : ℝ) : (∫ x, df (a t x) ∂μ) = ∫ x, df x ∂μ :=
    (hμ t).integral_comp (a t).measurableEmbedding df
  simp_rw [heq] at hint
  simpa using hint

theorem invariant_flow_l2_ibp
    (a : ℝ → X ≃ₜ X) (ha : Continuous (Function.uncurry (fun t x => a t x)))
    (ha0 : ∀ x, a 0 x = x) (hμ : ∀ t, MeasurePreserving (a t) μ μ)
    (u du v dv : X → ℂ) (hu : Continuous u) (hdu : Continuous du)
    (hv : Continuous v) (hdv : Continuous dv)
    (hu2 : MemLp u 2 μ) (hdu2 : MemLp du 2 μ)
    (hv2 : MemLp v 2 μ) (hdv2 : MemLp dv 2 μ)
    (hud : ∀ t x, HasDerivAt (fun s => u (a s x)) (du (a t x)) t)
    (hvd : ∀ t x, HasDerivAt (fun s => v (a s x)) (dv (a t x)) t) :
    (∫ x, star (du x) * v x ∂μ) = -(∫ x, star (u x) * dv x ∂μ) := by
  have hi0 : Integrable (fun x => star (u x) * v x) μ := hu2.star.integrable_mul hv2
  have hi1 : Integrable (fun x => star (du x) * v x) μ := hdu2.star.integrable_mul hv2
  have hi2 : Integrable (fun x => star (u x) * dv x) μ := hu2.star.integrable_mul hdv2
  have hz := integral_stationary_derivative_zero a ha ha0 hμ
    (fun x => star (u x) * v x)
    (fun x => star (du x) * v x + star (u x) * dv x)
    ((hdu.star.mul hv).add (hu.star.mul hdv)) hi0 (hi1.add hi2)
    (fun t x => (hud t x).star.mul (hvd t x))
  rw [integral_add hi1 hi2] at hz
  exact eq_neg_of_add_eq_zero_left hz

end DedekindZetaZeroFree.FourierContinuation.ResidualGlobalFlowIBP

end
