module

public import DedekindZetaZeroFree.LFunctions.Dedekind.GammaFactors
public import DedekindZetaZeroFree.Theta.Unfolding.MixedConeMellin
public import DedekindZetaZeroFree.Theta.Profiles.AngularAverageRegularityAndDecay

@[expose] public section

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace
open NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

private theorem exp_weight (s : ℂ) (x : ℝ) :
    (Real.exp x : ℂ) * (Real.exp x : ℂ) ^ (s - 1) = Complex.exp (s * x) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  ring
private theorem log_mellin (f : ℝ → ℂ) (s : ℂ) {c n : ℝ} (hc : 0 < c) (hn : 0 < n)
    (hi : Integrable (fun a : ℝ ↦ Complex.exp ((n : ℂ) * s * a) * f (c * Real.exp (n * a)))) :
    HasMellin f s ((n : ℂ) * (c : ℂ) ^ s *
      ∫ a : ℝ, Complex.exp ((n : ℂ) * s * a) * f (c * Real.exp (n * a))) := by
  let h := fun a : ℝ ↦ Complex.exp ((n : ℂ) * s * a) * f (c * Real.exp (n * a))
  let g := fun t : ℝ ↦ (t : ℂ) ^ (s - 1) * f t
  have heq (x : ℝ) : Real.exp x • g (Real.exp x) =
      (c : ℂ) ^ s * h ((x - Real.log c) / n) := by
    have ha : n * ((x - Real.log c) / n) = x - Real.log c := by field_simp
    have ht : c * Real.exp (n * ((x - Real.log c) / n)) = Real.exp x := by
      rw [ha, Real.exp_sub, Real.exp_log hc]
      field_simp
    dsimp [g, h]
    rw [ht, ← mul_assoc, exp_weight,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne'),
      ← Complex.ofReal_log hc.le, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hn.ne']
    <;> ring
  have hj : Integrable (fun x : ℝ ↦ h ((x - Real.log c) / n)) :=
    (hi.comp_div hn.ne').comp_sub_right (Real.log c)
  have hconv : MellinConvergent f s := by
    apply (integrable_comp_exp g).mp
    simpa only [heq] using hj.const_mul ((c : ℂ) ^ s)
  refine ⟨hconv, ?_⟩
  change (∫ t in Set.Ioi 0, g t) = _
  rw [← integral_comp_exp g]
  simp_rw [heq]
  rw [integral_const_mul, integral_sub_right_eq_self (fun x : ℝ ↦ h (x / n))]
  rw [Measure.integral_comp_div]
  simp only [abs_of_pos hn, Complex.real_smul]
  dsimp [h]
  ring
private theorem slab_coords (K : Type*) [Field K] [NumberField K]
    (a : ℝ) (u : Angular K) :
    unitSlabCoordinates (K := K) a u = angularLift K u + radialLift K a := by
  classical
  ext w
  by_cases hw : w = w₀ <;> simp [unitSlabCoordinates, unitRadialAngularEquiv,
    angularLift, radialLift, hw]

private theorem cov_pos (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) : 0 < mixedThetaCovolume K (FractionalIdeal.mk0 K J) := by
  unfold mixedThetaCovolume
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm]
  have hJ := Ideal.absNorm_ne_zero_of_nonZeroDivisors J
  have hd : (discr K : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero K
  positivity

private theorem class_centered_mellin (K : Type) [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun t : ℝ ↦ mixedAngularAverage K (FractionalIdeal.mk0 K J) t - 1) s
      ((Module.finrank ℚ K : ℂ) *
        (mixedThetaCovolume K (FractionalIdeal.mk0 K J) : ℂ) ^ s *
        ((2 : ℂ) ^ (-(↑(nrRealPlaces K + nrComplexPlaces K) : ℤ)) /
          ((Module.finrank ℚ K : ℂ) * (Units.regulator K : ℂ)) *
          Complex.Gammaℝ s ^ nrRealPlaces K * Complex.Gammaℂ s ^ nrComplexPlaces K *
          fundamentalConeZeta K J s)) := by
  classical
  let I := FractionalIdeal.mk0 K J
  let n : ℝ := Module.finrank ℚ K
  let c := mixedThetaCovolume K I
  let F := fun y : realSpace K ↦ Complex.exp ((n : ℂ) * s * (y w₀ : ℂ)) *
    (fractionalShapeIdealTheta K I (NumberField.mixedEmbedding.fundamentalCone.expMapBasis y)
      (fun w ↦ ne_of_gt (NumberField.mixedEmbedding.fundamentalCone.expMapBasis_pos _ w)) - 1)
  have hn : 0 < n := by dsimp [n]; exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  have hc : 0 < c := cov_pos K J
  have hi : IntegrableOn F (DedekindZetaZeroFree.Theta.unitFundamentalParamSet K) :=
    integrableOn_fractionalShapeIdealTheta_logMellin K J hs
  have hip : Integrable (fun p : ℝ × Angular K ↦ F (unitSlabCoordinates p.1 p.2))
      ((volume : Measure ℝ).prod ((volume : Measure (Angular K)).restrict (angularCube K))) := by
    have h := (integrableOn_radialSlab_iff F Set.univ).mp (by simpa using hi)
    unfold IntegrableOn at h
    rw [← Measure.prod_restrict, Measure.restrict_univ] at h
    exact h
  have hcoord (a : ℝ) (u : Angular K) :
      fractionalShapeIdealTheta K I
        (NumberField.mixedEmbedding.fundamentalCone.expMapBasis (unitSlabCoordinates a u))
        (fun w ↦ ne_of_gt (NumberField.mixedEmbedding.fundamentalCone.expMapBasis_pos _ w)) =
        mixedRadialTheta K I (c * Real.exp (n * a)) u := by
    have ht : (Real.log (c * Real.exp (n * a)) - Real.log c) / n = a := by
      rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp]
      field_simp
      ring
    unfold mixedRadialTheta
    congr 1
    unfold mixedThetaShape
    change _ = NumberField.mixedEmbedding.fundamentalCone.expMapBasis
      (angularLift K u + radialLift K ((Real.log (c * Real.exp (n * a)) - Real.log c) / n))
    rw [ht, slab_coords]
  have hinner (a : ℝ) : (∫ u in angularCube K, F (unitSlabCoordinates a u)) =
      Complex.exp ((n : ℂ) * s * a) * (mixedAngularAverage K I (c * Real.exp (n * a)) - 1) := by
    have ht : 0 < c * Real.exp (n * a) := mul_pos hc (Real.exp_pos _)
    rw [mixedAngularAverage_sub_one K I _ ht, ← integral_const_mul]
    apply setIntegral_congr_fun (measurableSet_unitAngularParamSet (K := K))
    intro u hu
    dsimp [F]
    rw [unitSlabCoordinates_apply_w₀, hcoord]
  have havg := hip.integral_prod_left
  have hi' : Integrable (fun a : ℝ ↦ Complex.exp ((n : ℂ) * s * a) *
      (mixedAngularAverage K I (c * Real.exp (n * a)) - 1)) := by
    simpa only [hinner] using havg
  have hm := log_mellin (fun t ↦ mixedAngularAverage K I t - 1) s hc hn hi'
  have hint := setIntegral_unitFundamentalParamSet_eq_radialAngular F hi
  change (∫ y in DedekindZetaZeroFree.Theta.unitFundamentalParamSet K, F y) =
    ∫ a : ℝ, ∫ u in angularCube K, F (unitSlabCoordinates a u) at hint
  simp only [hinner] at hint
  rw [← hint] at hm
  have hcone := setIntegral_fractionalShapeIdealTheta_logMellin K J hs
  change (∫ y in DedekindZetaZeroFree.Theta.unitFundamentalParamSet K, F y) = _ at hcone
  rw [hcone] at hm
  exact hm
private theorem cov_cpow (K : Type) [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    (mixedThetaCovolume K (FractionalIdeal.mk0 K J) : ℂ) ^ s =
      (Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ) ^ s *
        (((|discr K| : ℤ) : ℂ) ^ (s / 2)) := by
  have hN : 0 < (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors J)
  have hD : 0 < |(discr K : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero K)
  unfold mixedThetaCovolume
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm]
  rw [Complex.ofReal_mul, Rat.cast_natCast]
  change (((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) *
    (Real.sqrt |(discr K : ℝ)| : ℂ)) ^ s = _
  rw [Complex.mul_cpow_ofReal_nonneg hN.le (Real.sqrt_nonneg _)]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hD).ne'),
    ← Complex.ofReal_log (Real.sqrt_nonneg _), Real.log_sqrt hD.le]
  have hd : ((|discr K| : ℤ) : ℂ) = Complex.ofReal |(discr K : ℝ)| := by norm_cast
  rw [hd, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    ← Complex.ofReal_log hD.le]
  congr 1
  push_cast
  ring

private theorem normalized_calibration (K : Type) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    (alpha K : ℂ) *
      ((Module.finrank ℚ K : ℂ) *
        (mixedThetaCovolume K (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) : ℂ) ^ s *
        ((2 : ℂ) ^ (-(↑(nrRealPlaces K + nrComplexPlaces K) : ℤ)) /
          ((Module.finrank ℚ K : ℂ) * (Units.regulator K : ℂ)) *
          Complex.Gammaℝ s ^ nrRealPlaces K * Complex.Gammaℂ s ^ nrComplexPlaces K *
          fundamentalConeZeta K (inverseClassIdealRepresentative K C) s)) =
        zetaGammaFactor K s * partialDedekindZeta K C s := by
  have hn : (Module.finrank ℚ K : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hr : (Units.regulator K : ℂ) ≠ 0 := by
    exact_mod_cast (Units.regulator_pos K).ne'
  have hw : (Units.torsionOrder K : ℂ) ≠ 0 := by
    exact_mod_cast Units.torsionOrder_ne_zero K
  rw [partialDedekindZeta_eq_normalized_fundamentalConeZeta K C hs,
    cov_cpow K _ s]
  unfold alpha zetaGammaFactor
  push_cast
  rw [← Nat.cast_add (R := ℤ), zpow_neg, zpow_natCast]
  field_simp [hn, hr, hw]
  <;> ring

theorem hasMellin_classTheta (K : Type) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    HasMellin
      (fun t : ℝ ↦ (alpha K : ℂ) *
        (mixedAngularAverage K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) t - 1))
      s (zetaGammaFactor K s * partialDedekindZeta K C s) := by
  have hm := class_centered_mellin K (inverseClassIdealRepresentative K C) hs
  have hscalar := hasMellin_const_smul hm.1 (alpha K : ℂ)
  change HasMellin _ s ((alpha K : ℂ) * _) at hscalar
  rw [hm.2, normalized_calibration K C hs] at hscalar
  exact hscalar

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
