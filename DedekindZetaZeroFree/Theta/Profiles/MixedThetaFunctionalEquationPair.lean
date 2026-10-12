module

public import DedekindZetaZeroFree.Theta.Profiles.AngularAverageRegularityAndDecay
public import DedekindZetaZeroFree.Theta.Profiles.CenteredPoissonSummation
public import DedekindZetaZeroFree.LFunctions.Dedekind.IdealClassConeSeries

@[expose] public section

noncomputable section

open Classical NumberField
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

theorem mixedThetaPair_primal_integrable (K : Type) [Field K] [NumberField K] :
    MeasureTheory.LocallyIntegrableOn (fun t ↦ (alpha K : ℂ) *
      ∑ C : ClassGroup (𝓞 K), mixedAngularAverage K
        (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) t) (Set.Ioi 0) := by
  apply (MeasureTheory.locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).mpr
  intro s hs hsc
  apply MeasureTheory.Integrable.const_mul
  apply MeasureTheory.integrable_finset_sum
  intro C _
  exact (locallyIntegrableOn_mixedAngularAverage K
    (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))).integrableOn_compact_subset
      hs hsc

theorem mixedThetaPair_dual_integrable (K : Type) [Field K] [NumberField K] :
    MeasureTheory.LocallyIntegrableOn (fun t ↦ (alpha K : ℂ) *
      ∑ C : ClassGroup (𝓞 K), mixedNegAngularAverage K
        (traceDualIdealUnit K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))) t) (Set.Ioi 0) := by
  apply (MeasureTheory.locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).mpr
  intro s hs hsc
  apply MeasureTheory.Integrable.const_mul
  apply MeasureTheory.integrable_finset_sum
  intro C _
  exact (locallyIntegrableOn_mixedNegAngularAverage K
    (traceDualIdealUnit K
      (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)))).integrableOn_compact_subset
        hs hsc

def mixedThetaPair (K : Type) [Field K] [NumberField K] : WeakFEPair ℂ where
  f := fun t ↦ (alpha K : ℂ) *
    ∑ C : ClassGroup (𝓞 K),
      mixedAngularAverage K
        (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) t
  g := fun t ↦ (alpha K : ℂ) *
    ∑ C : ClassGroup (𝓞 K),
      mixedNegAngularAverage K
        (traceDualIdealUnit K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))) t
  k := 1
  ε := 1
  f₀ := (alpha K : ℂ) * (Fintype.card (ClassGroup (𝓞 K)) : ℂ)
  g₀ := (alpha K : ℂ) * (Fintype.card (ClassGroup (𝓞 K)) : ℂ)
  hk := by norm_num
  hε := by norm_num
  hf_int := mixedThetaPair_primal_integrable K
  hg_int := mixedThetaPair_dual_integrable K
  h_feq := by
    intro x hx
    simp only [Real.rpow_one, one_mul, smul_eq_mul]
    simp_rw [mixedAngularAverage_poisson K _ x hx]
    rw [← Finset.mul_sum]
    ring
  hf_top := by
    intro r
    have h := (Asymptotics.IsBigO.sum (s := Finset.univ)
      (fun C _ ↦ mixedAngularAverage_isBigO_rpow K
        (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) r)).const_mul_left
          (alpha K : ℂ)
    simpa only [Finset.sum_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, mul_sub] using h
  hg_top := by
    intro r
    have h := (Asymptotics.IsBigO.sum (s := Finset.univ)
      (fun C _ ↦ mixedNegAngularAverage_isBigO_rpow K
        (traceDualIdealUnit K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))) r)).const_mul_left
            (alpha K : ℂ)
    simpa only [Finset.sum_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, mul_sub] using h

@[simp] theorem mixedThetaPair_k (K : Type) [Field K] [NumberField K] :
    (mixedThetaPair K).k = 1 := rfl

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
