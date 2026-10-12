module

public import DedekindZetaZeroFree.LFunctions.Dedekind.IdealClassThetaMellin
public import DedekindZetaZeroFree.Theta.Profiles.MixedThetaFunctionalEquationPair

@[expose] public section

noncomputable section

open Classical NumberField
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

private lemma mixedThetaPair_f (K : Type) [Field K] [NumberField K] :
    (mixedThetaPair K).f = fun t => (alpha K : ℂ) *
      ∑ C : ClassGroup (𝓞 K),
        mixedAngularAverage K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) t := rfl

private lemma mixedThetaPair_f0 (K : Type) [Field K] [NumberField K] :
    (mixedThetaPair K).f₀ = (alpha K : ℂ) * (Fintype.card (ClassGroup (𝓞 K)) : ℂ) := rfl

private lemma hasMellin_finset_sum {s : ℂ} {ι : Type*} (t : Finset ι)
    (f : ι → ℝ → ℂ) (m : ι → ℂ)
    (h : ∀ i ∈ t, HasMellin (f i) s (m i)) :
    HasMellin (fun x => ∑ i ∈ t, f i x) s (∑ i ∈ t, m i) := by
  classical
  induction t using Finset.induction with
  | empty =>
      constructor
      · show MeasureTheory.IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (0 : ℂ)) (Set.Ioi 0)
        simpa using (MeasureTheory.integrableOn_zero
          (f := fun _ : ℝ => (0 : ℂ)) (s := Set.Ioi 0) (μ := volume))
      · simp [mellin]
  | insert a t ha ih =>
      have hfa := h a (Finset.mem_insert_self a t)
      have hft : ∀ i ∈ t, HasMellin (f i) s (m i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have ih' := ih hft
      have hadd := hasMellin_add hfa.1 ih'.1
      rw [hfa.2, ih'.2] at hadd
      convert hadd using 2
      · exact Finset.sum_insert ha
      · exact Finset.sum_insert ha

theorem hasMellin_mixedThetaPair (K : Type) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun t : ℝ ↦ (mixedThetaPair K).f t - (mixedThetaPair K).f₀)
      s (zetaGammaFactor K s * NumberField.dedekindZeta K s) := by

  have hfun : (fun t : ℝ ↦ (mixedThetaPair K).f t - (mixedThetaPair K).f₀) =
      (fun t => ∑ C : ClassGroup (𝓞 K), (alpha K : ℂ) *
        (mixedAngularAverage K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) t - 1)) := by
    rw [mixedThetaPair_f, mixedThetaPair_f0]
    funext t
    conv_rhs => rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    ring
  rw [hfun]

  have h := hasMellin_finset_sum (Finset.univ : Finset (ClassGroup (𝓞 K)))
    (fun C t => (alpha K : ℂ) *
      (mixedAngularAverage K
        (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) t - 1))
    (fun C => zetaGammaFactor K s * partialDedekindZeta K C s)
    (fun C _ => hasMellin_classTheta K C hs)

  rw [show (∑ C : ClassGroup (𝓞 K), zetaGammaFactor K s * partialDedekindZeta K C s)
      = zetaGammaFactor K s * NumberField.dedekindZeta K s by
    rw [← Finset.mul_sum, sum_partialDedekindZeta K hs]] at h
  exact h

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
