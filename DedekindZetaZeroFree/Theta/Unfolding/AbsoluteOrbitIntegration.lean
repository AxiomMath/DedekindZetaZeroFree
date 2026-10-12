module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DedekindZetaZeroFree.OrbitExpansion.AbsoluteIntegration
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]
  {μ : Measure X} {f : ι → X → ℂ}

theorem absolute_mass_finite (hi : ∀ i, Integrable (f i) μ)
    (hs : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    (∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ) < ⊤ := by
  rw [lintegral_tsum (fun i => (hi i).aestronglyMeasurable.enorm)]
  have he (i : ι) : (∫⁻ x, ‖f i x‖ₑ ∂μ) = ENNReal.ofReal (∫ x, ‖f i x‖ ∂μ) := by
    simpa only [enorm_eq_nnnorm, coe_nnnorm] using lintegral_coe_eq_integral
      (fun x => ‖f i x‖₊) (hi i).norm
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg (fun x => norm_nonneg _)) hs]
  exact ENNReal.ofReal_lt_top

theorem norm_sum_ae (hi : ∀ i, Integrable (f i) μ)
    (hs : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    ∀ᵐ x ∂μ, Summable (fun i => ‖f i x‖) := by
  have hm := absolute_mass_finite hi hs
  filter_upwards [ae_lt_top' (AEMeasurable.tsum
    (fun i => (hi i).aestronglyMeasurable.enorm)) hm.ne] with x hx
  exact tsum_enorm_ne_top_iff_summable_norm.mp hx.ne

theorem integrable_sum (hi : ∀ i, Integrable (f i) μ)
    (hs : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, f i x) μ := by
  have hm := absolute_mass_finite hi hs
  refine ⟨AEStronglyMeasurable.tsum (fun i => (hi i).aestronglyMeasurable), ?_⟩
  exact lt_of_le_of_lt (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)) hm

theorem hasSum_integral {g : X → ℂ} (hi : ∀ i, Integrable (f i) μ)
    (hs : Summable (fun i => ∫ x, ‖f i x‖ ∂μ))
    (hg : ∀ᵐ x ∂μ, HasSum (fun i => f i x) (g x)) :
    Integrable g μ ∧ HasSum (fun i => ∫ x, f i x ∂μ) (∫ x, g x ∂μ) := by
  have he : (fun x => ∑' i, f i x) =ᵐ[μ] g := hg.mono (fun _ h => h.tsum_eq)
  refine ⟨(integrable_sum hi hs).congr he, ?_⟩
  have hh := hasSum_integral_of_summable_integral_norm hi hs
  rw [integral_congr_ae he] at hh
  exact hh

theorem summable_majorant_ae {b : ι → X → ℝ}
    (hi : ∀ i, Integrable (b i) μ) (hp : ∀ i x, 0 ≤ b i x)
    (hs : Summable (fun i => ∫ x, b i x ∂μ)) :
    ∀ᵐ x ∂μ, Summable (fun i => b i x) := by
  have hi' (i : ι) : Integrable (fun x => (b i x : ℂ)) μ := (hi i).ofReal
  have hn (i : ι) (x : X) : ‖(b i x : ℂ)‖ = b i x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp i x)]
  have h := norm_sum_ae hi' (by simpa only [hn] using hs)
  simpa only [hn] using h

end DedekindZetaZeroFree.OrbitExpansion.AbsoluteIntegration

end
