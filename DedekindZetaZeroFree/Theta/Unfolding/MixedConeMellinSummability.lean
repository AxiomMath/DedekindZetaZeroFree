module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.MixedGaussianProduct
public import DedekindZetaZeroFree.LFunctions.Dedekind.IdealClassConeSeries

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open DedekindZetaZeroFree.Theta
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

theorem summable_integral_norm_mixedMellinGaussian_idealSet
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun a : idealSet K J ↦
      ∫ q : InfinitePlace K → ℝ,
        ‖mixedMellinGaussian K (idealSetElement K J a) s q‖
        ∂Measure.pi (fun _v : InfinitePlace K ↦
          (volume : Measure ℝ).restrict (Set.Ioi 0))) := by
  have hbase := (summable_idealSet_inverseNormPower K J (s := (s.re : ℂ)) hs).norm
  refine (hbase.mul_left ((1 / 2 : ℝ) ^ nrRealPlaces K *
    (1 / 4 : ℝ) ^ nrComplexPlaces K *
    ‖Complex.Gammaℝ (s.re : ℂ)‖ ^ nrRealPlaces K *
    ‖Complex.Gammaℂ (s.re : ℂ)‖ ^ nrComplexPlaces K)).congr fun a ↦ ?_
  rw [integral_norm_mixedMellinGaussian K (idealSetElement K J a) (idealSetElement_ne_zero K J a) s
    (lt_trans zero_lt_one hs)]
  rw [absNorm_idealSetElement K J a]
  rw [← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (idealSetIntNorm_ne_zero K J a)))]
  simp

theorem hasSum_integral_mixedMellinGaussian_idealSet
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun a : idealSet K J ↦
      ∫ q : InfinitePlace K → ℝ,
        mixedMellinGaussian K (idealSetElement K J a) s q
        ∂Measure.pi (fun _v : InfinitePlace K ↦
          (volume : Measure ℝ).restrict (Set.Ioi 0)))
      (((1 / 2 : ℂ) ^ nrRealPlaces K *
          (1 / 4 : ℂ) ^ nrComplexPlaces K *
          Complex.Gammaℝ s ^ nrRealPlaces K *
          Complex.Gammaℂ s ^ nrComplexPlaces K) *
        fundamentalConeZeta K J s) := by
  have h := (hasSum_idealSet_inverseNormPower K J hs).mul_left
    ((1 / 2 : ℂ) ^ nrRealPlaces K *
      (1 / 4 : ℂ) ^ nrComplexPlaces K *
      Complex.Gammaℝ s ^ nrRealPlaces K *
      Complex.Gammaℂ s ^ nrComplexPlaces K)
  refine h.congr_fun fun a ↦ ?_
  rw [integral_mixedMellinGaussian K (idealSetElement K J a) (idealSetElement_ne_zero K J a) s
    (lt_trans zero_lt_one hs)]
  congr 2
  exact_mod_cast absNorm_idealSetElement K J a

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
