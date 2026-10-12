module

public import DedekindZetaZeroFree.Theta.Profiles.MixedThetaDefinitions

@[expose] public section

noncomputable section

open Classical MeasureTheory NumberField
open NumberField.mixedEmbedding.fundamentalCone
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

open NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem

private theorem centeredCovolume_pos (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < mixedThetaCovolume K I := by
  have hI : 0 < FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) :=
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm
      (FractionalIdeal.absNorm_eq_zero_iff.not.mpr (Units.ne_zero I)))
  have hd : 0 < |(discr K : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero K)
  exact mul_pos (by exact_mod_cast hI) (Real.sqrt_pos.mpr hd)

private theorem centeredShape_prod (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (ht : 0 < t) (u : Angular K) :
    (∏ w : {w : InfinitePlace K // IsReal w}, mixedThetaShape K I t u w.1) *
      ∏ w : {w : InfinitePlace K // IsComplex w}, (mixedThetaShape K I t u w.1)^2 =
        t / mixedThetaCovolume K I := by
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hp := prod_expMapBasis_pow (angularLift K u +
    radialLift K ((Real.log t - Real.log (mixedThetaCovolume K I)) /
      (Module.finrank ℚ K : ℝ)))
  rw [prod_eq_prod_mul_prod] at hp
  simp only [mult_isReal, mult_isComplex, pow_one] at hp
  change _ = _ at hp
  rw [show (angularLift K u + radialLift K
      ((Real.log t - Real.log (mixedThetaCovolume K I)) /
        (Module.finrank ℚ K : ℝ))) w₀ =
      (Real.log t - Real.log (mixedThetaCovolume K I)) /
        (Module.finrank ℚ K : ℝ) by simp [angularLift, radialLift]] at hp
  rw [← Real.exp_nat_mul, mul_div_cancel₀ _ hn, Real.exp_sub,
    Real.exp_log ht, Real.exp_log (centeredCovolume_pos K I)] at hp
  exact hp

theorem covolume_shapeIdealLattice_mixedThetaShape
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (ht : 0 < t) (u : Angular K) :
    ZLattice.covolume
      (shapeIdealLattice K I (mixedThetaShape K I t u)
        (fun v ↦ ne_of_gt (expMapBasis_pos _ v))) volume = t := by
  rw [covolume_shapeIdealLattice, centeredShape_prod K I t ht u,
    abs_of_pos (div_pos ht (centeredCovolume_pos K I))]
  exact div_mul_cancel₀ t (ne_of_gt (centeredCovolume_pos K I))

private theorem centeredCovolume_dual (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    mixedThetaCovolume K (traceDualIdealUnit K I) = (mixedThetaCovolume K I)⁻¹ := by
  have hI : (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.mpr (Units.ne_zero I))
  have hd : |(discr K : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast discr_ne_zero K)
  have hs := Real.sq_sqrt (abs_nonneg (discr K : ℝ))
  have hs0 : Real.sqrt |(discr K : ℝ)| ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd)))
  unfold mixedThetaCovolume
  rw [absNorm_traceDualIdealUnit, absNorm_traceDual_one]
  push_cast
  rw [mul_inv_rev]
  field_simp
  nlinarith [hs]

private theorem centeredShape_inverse (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (u : Angular K) :
    (fun w ↦ (mixedThetaShape K I (1 / t) u w)⁻¹) =
      mixedThetaShape K (traceDualIdealUnit K I) t (-u) := by
  have hx : angularLift K (-u) + radialLift K
      ((Real.log t - Real.log (mixedThetaCovolume K (traceDualIdealUnit K I))) /
        (Module.finrank ℚ K : ℝ)) =
      -(angularLift K u + radialLift K
        ((Real.log (1 / t) - Real.log (mixedThetaCovolume K I)) /
          (Module.finrank ℚ K : ℝ))) := by
    rw [centeredCovolume_dual, one_div, Real.log_inv, Real.log_inv]
    ext w
    simp only [Pi.add_apply, Pi.neg_apply, angularLift, radialLift]
    split_ifs <;> simp <;> ring
  unfold mixedThetaShape
  rw [hx, expMapBasis_apply, expMapBasis_apply, map_neg]
  ext w
  simp [expMap_apply, Real.exp_neg]

theorem mixedRadialTheta_poisson
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (ht : 0 < t) (u : Angular K) :
    mixedRadialTheta K I (1 / t) u =
      (t : ℂ) * mixedRadialTheta K (traceDualIdealUnit K I) t (-u) := by
  unfold mixedRadialTheta
  rw [fractionalShapeIdealTheta_poissonSummation,
    covolume_shapeIdealLattice_mixedThetaShape K I (1 / t) (one_div_pos.mpr ht) u]
  have hq := centeredShape_inverse K I t u
  simp_rw [hq]
  simp [NNReal.smul_def, Real.toNNReal_of_nonneg (le_of_lt (one_div_pos.mpr ht)),
    max_eq_left (le_of_lt (inv_pos.mpr ht)), ht.ne']

theorem mixedAngularAverage_poisson
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (ht : 0 < t) :
    mixedAngularAverage K I (1 / t) =
      (t : ℂ) * mixedNegAngularAverage K (traceDualIdealUnit K I) t := by
  unfold mixedAngularAverage mixedNegAngularAverage
  simp_rw [mixedRadialTheta_poisson K I t ht]
  exact integral_const_mul _ _

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
