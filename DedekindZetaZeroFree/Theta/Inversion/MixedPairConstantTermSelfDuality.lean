module

public import DedekindZetaZeroFree.Theta.Profiles.MixedThetaFunctionalEquationPair
public import DedekindZetaZeroFree.Arithmetic.Ideals.TraceDualClassInvolution
public import DedekindZetaZeroFree.Theta.Periods.AngularAverageClassInvariance

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

theorem mixedThetaPair_selfdual (F : Type) [Field F] [NumberField F] :
    ∀ t : ℝ, 0 < t →
      (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).f t =
        (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).g t := by
  intro t ht
  change (_ : ℂ) * ∑ C : ClassGroup (NumberField.RingOfIntegers F),
      DedekindZetaZeroFree.AbelianQuotient.Theta.mixedAngularAverage F
        (FractionalIdeal.mk0 F
          (DedekindZetaZeroFree.AbelianQuotient.Theta.inverseClassIdealRepresentative F C)) t =
    (_ : ℂ) * ∑ C : ClassGroup (NumberField.RingOfIntegers F),
      DedekindZetaZeroFree.AbelianQuotient.Theta.mixedNegAngularAverage F
        (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F
          (FractionalIdeal.mk0 F
            (DedekindZetaZeroFree.AbelianQuotient.Theta.inverseClassIdealRepresentative F C))) t
  congr 1
  symm
  calc
    _ = ∑ C : ClassGroup (NumberField.RingOfIntegers F),
        DedekindZetaZeroFree.AbelianQuotient.Theta.mixedAngularAverage F
          (FractionalIdeal.mk0 F
            (DedekindZetaZeroFree.AbelianQuotient.Theta.inverseClassIdealRepresentative F
              (principalTraceDualClassEquiv F C))) t := by
      apply Finset.sum_congr rfl
      intro C _
      rw [mixedNegAngularAverage_eq_mixedAngularAverage F _ t ht]
      exact mixedAngularAverage_class_invariant F _ _
        (mk_traceDual_inverseClassIdealRepresentative F C) t ht
    _ = _ := (principalTraceDualClassEquiv F).sum_comp
      (fun C ↦ DedekindZetaZeroFree.AbelianQuotient.Theta.mixedAngularAverage F
        (FractionalIdeal.mk0 F
          (DedekindZetaZeroFree.AbelianQuotient.Theta.inverseClassIdealRepresentative F C)) t)

@[simp] theorem mixedThetaPair_k (F : Type) [Field F] [NumberField F] :
    (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).k = 1 := rfl

@[simp] theorem mixedThetaPair_ε (F : Type) [Field F] [NumberField F] :
    (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).ε = 1 := rfl

@[simp] theorem mixedThetaPair_f₀_eq_g₀ (F : Type) [Field F] [NumberField F] :
    (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).f₀ =
      (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).g₀ := rfl

end DedekindZetaZeroFree.Hecke
