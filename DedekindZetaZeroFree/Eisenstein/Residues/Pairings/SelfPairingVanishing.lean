module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Residual.OrderedDifferentialAdjoints

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem integral_pairing_finite_left {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (f : ι → X → ℂ) (g : X → ℂ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, star (∑ i ∈ s, a i * f i x) * g x ∂μ) =
      ∑ i ∈ s, star (a i) * ∫ x, star (f i x) * g x ∂μ := by
  simp_rw [star_sum, star_mul, Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = ∫ x, star (a i) * (star (f i x) * g x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := integral_const_mul _ _
  · intro i hi
    have hh := ((hf i hi).star.integrable_mul hg).const_mul (star (a i))
    convert hh using 1
    funext x
    simp only [Pi.mul_apply, Pi.star_apply]
    ring

theorem continuous_zero_of_pairing_self_zero [TopologicalSpace X]
    [μ.IsOpenPosMeasure] (f : X → ℂ) (hc : Continuous f) (hf : MemLp f 2 μ)
    (hz : (∫ x, star (f x) * f x ∂μ) = 0) : f = 0 := by
  have hi : inner ℂ (hf.toLp f) (hf.toLp f) = 0 := by
    calc
      inner ℂ (hf.toLp f) (hf.toLp f) = ∫ x, star (f x) * f x ∂μ := by
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp] with x hx
        rw [hx]
        rw [RCLike.inner_apply]
        exact mul_comm _ _
      _ = 0 := hz
  have he : hf.toLp f = 0 := inner_self_eq_zero.mp hi
  have hae : f =ᵐ[μ] (0 : X → ℂ) := by
    apply (hf.toLp_eq_toLp_iff (MemLp.zero : MemLp (0 : X → ℂ) 2 μ)).mp
    simpa using he
  exact MeasureTheory.Measure.eq_of_ae_eq hae hc continuous_const

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
theorem original_zero_of_pairing_self_zero
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (f : smoothAllWordL2 R)
    (hz : (∫ x, star (f.val x) * f.val x ∂ R.quotientHaar) = 0) : f.val = 0 := by
  letI := (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1
  exact continuous_zero_of_pairing_self_zero R.quotientHaar f.val
    (f.property []).1.1 (f.property []).2 hz

end DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy

end
