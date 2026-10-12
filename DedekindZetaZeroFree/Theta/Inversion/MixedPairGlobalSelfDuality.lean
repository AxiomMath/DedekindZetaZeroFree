module

public import DedekindZetaZeroFree.Theta.Inversion.MixedPairConstantTermSelfDuality

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

theorem mixedThetaPair_global_selfDual (F : Type) [Field F] [NumberField F] :
    (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).g =
      (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).f := by
  funext t
  calc
    (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).g t =
        (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).g
          (Real.exp (Real.log t)) := by
      simp only [DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair,
        DedekindZetaZeroFree.AbelianQuotient.Theta.mixedNegAngularAverage,
        DedekindZetaZeroFree.AbelianQuotient.Theta.mixedRadialTheta,
        DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaShape, Real.log_exp]
    _ = (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).f
          (Real.exp (Real.log t)) :=
      (mixedThetaPair_selfdual F _ (Real.exp_pos _)).symm
    _ = (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).f t := by
      simp only [DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair,
        DedekindZetaZeroFree.AbelianQuotient.Theta.mixedAngularAverage,
        DedekindZetaZeroFree.AbelianQuotient.Theta.mixedRadialTheta,
        DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaShape, Real.log_exp]

theorem mixedThetaPair_global_g₀_eq_f₀ (F : Type) [Field F] [NumberField F] :
    (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).g₀ =
      (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).f₀ := by
  rfl

theorem mixedThetaPair_global_ε_eq_one (F : Type) [Field F] [NumberField F] :
    (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).ε = 1 := by
  rfl

end DedekindZetaZeroFree.Hecke
