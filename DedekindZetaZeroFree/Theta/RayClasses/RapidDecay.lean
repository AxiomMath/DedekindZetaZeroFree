module

public import DedekindZetaZeroFree.Theta.RayClasses.AveragedContinuity
public import DedekindZetaZeroFree.Theta.RayClasses.ZeroModeTail
public import DedekindZetaZeroFree.Analysis.StretchedExponentialDecay

@[expose] public section

noncomputable section

open MeasureTheory

namespace DedekindZetaZeroFree.AbelianQuotient.RayTheta

variable {K : Type} [Field K] [NumberField K]

theorem locallyIntegrableOn_fδ
    (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) :
    LocallyIntegrableOn (fδ D δ) (Set.Ioi (0 : ℝ)) volume := by
  exact DedekindZetaZeroFree.rayTheta_locallyIntegrableOn_fδ D δ

theorem locallyIntegrableOn_gδDual
    (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) :
    LocallyIntegrableOn (gδDual D δ) (Set.Ioi (0 : ℝ)) volume := by
  exact DedekindZetaZeroFree.rayTheta_locallyIntegrableOn_gδDual D δ

theorem fδ_sub_f0δ_isBigO_rpow
    (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) (r : ℝ) :
    Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ => fδ D δ t - f0δ D δ)
      (fun t : ℝ => t ^ r) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := DedekindZetaZeroFree.rayTheta_zeroModeTail K D δ
  have hp : 0 < 2 / (Module.finrank ℚ K : ℝ) := by
    apply div_pos (by norm_num)
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have h := DedekindZetaZeroFree.thetaStretchedExponentialPower_bound
    (2 / (Module.finrank ℚ K : ℝ)) B hp hB
    (fun t : ℝ => fδ D δ t - f0δ D δ) A hA.le
    (fun t ht => (hbound t ht).1) r
  simpa only [Real.rpow_eq_pow] using h

theorem gδDual_sub_g0δ_isBigO_rpow
    (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) (r : ℝ) :
    Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ => gδDual D δ t - g0δ D δ)
      (fun t : ℝ => t ^ r) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := DedekindZetaZeroFree.rayTheta_zeroModeTail K D δ
  have hp : 0 < 2 / (Module.finrank ℚ K : ℝ) := by
    apply div_pos (by norm_num)
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have h := DedekindZetaZeroFree.thetaStretchedExponentialPower_bound
    (2 / (Module.finrank ℚ K : ℝ)) B hp hB
    (fun t : ℝ => gδDual D δ t - g0δ D δ) A hA.le
    (fun t ht => (hbound t ht).2) r
  simpa only [Real.rpow_eq_pow] using h

end DedekindZetaZeroFree.AbelianQuotient.RayTheta

end
