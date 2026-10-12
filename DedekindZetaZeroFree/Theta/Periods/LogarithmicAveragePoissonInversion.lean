module

public import DedekindZetaZeroFree.Theta.Periods.LogarithmicAverageClassInvariance
public import DedekindZetaZeroFree.Theta.Profiles.CenteredPoissonSummation

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable (F : Type) [Field F] [NumberField F]

theorem topLogIdealAverage_poisson
    (htop : (⊤ : Ideal (𝓞 F)) ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t) :
    topLogIdealAverage F htop I (1 / t) =
      (t : ℂ) * topLogIdealAverage F htop
        (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F I) t := by
  have hpoint (h : RayCoset.logHyperplane F) :
      centeredLogIdealTheta F I (1 / t) h =
        (t : ℂ) * centeredLogIdealTheta F
          (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F I) t (-h) := by
    rw [centeredLogIdealTheta_eq_mixedRadialTheta F I (1 / t) (one_div_pos.mpr ht),
      DedekindZetaZeroFree.AbelianQuotient.Theta.mixedRadialTheta_poisson F I t ht,
      centeredLogIdealTheta_eq_mixedRadialTheta F _ t ht, map_neg]
  unfold topLogIdealAverage
  simp_rw [hpoint]
  rw [MeasureTheory.integral_const_mul]
  rw [← mul_assoc, mul_comm _ (t : ℂ), mul_assoc]
  congr 1
  exact topLogIdealAverage_reflection F htop _ t ht

end DedekindZetaZeroFree.Hecke.Theta

end
