module

public import DedekindZetaZeroFree.Theta.Profiles.MixedGaussian

@[expose] public section

noncomputable section

open Classical NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

def mixedMellinGaussian (x : K) (s : ℂ) (q : InfinitePlace K → ℝ) : ℂ :=
  ∏ v : InfinitePlace K,
    (q v : ℂ) ^ ((v.mult : ℂ) * s - 1) *
      Complex.exp (-(Real.pi : ℂ) * (v.mult : ℂ) *
        (q v : ℂ) ^ 2 * (v x : ℂ) ^ 2)

def mixedRadialJacobian (y : realSpace K) : ℝ :=
  Real.exp ((Module.finrank ℚ K : ℝ) * y Units.dirichletUnitTheorem.w₀) *
    (∏ v : {v : InfinitePlace K // IsComplex v}, expMapBasis y v.1)⁻¹ *
      (2 : ℝ)⁻¹ ^ nrComplexPlaces K * (Module.finrank ℚ K : ℝ) * regulator K

private theorem radialJacobian_eq_prod (y : realSpace K) :
    mixedRadialJacobian K y = (∏ v, expMapBasis y v) *
      ((2 : ℝ)⁻¹ ^ nrComplexPlaces K * (Module.finrank ℚ K : ℝ) * regulator K) := by
  have hp : Real.exp ((Module.finrank ℚ K : ℝ) * y dirichletUnitTheorem.w₀) =
      (∏ v, expMapBasis y v) *
        (∏ v : {v : InfinitePlace K // IsComplex v}, expMapBasis y v.1) := by
    rw [Real.exp_nat_mul, ← prod_expMapBasis_pow,
      prod_eq_prod_mul_prod, prod_eq_prod_mul_prod (fun v ↦ expMapBasis y v)]
    simp only [mult_isReal, mult_isComplex, pow_one, Finset.prod_pow]
    ring
  unfold mixedRadialJacobian
  rw [hp]
  have hn : (∏ v : {v : InfinitePlace K // IsComplex v}, expMapBasis y v.1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ ↦ (expMapBasis_pos y v.1).ne'
  field_simp
  <;> ring

private theorem weighted_log_sum (y : realSpace K) :
    ∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (expMapBasis y v) =
      (Module.finrank ℚ K : ℝ) * y dirichletUnitTheorem.w₀ := by
  have h := congrArg Real.log (prod_expMapBasis_pow y)
  rw [Real.log_prod (fun v _ ↦ pow_ne_zero _ (expMapBasis_pos y v).ne'),
    Real.log_pow, Real.log_exp] at h
  simpa only [Real.log_pow] using h

theorem mixedRadialJacobian_mul_mixedMellinGaussian
    (y : realSpace K) (x : K) (s : ℂ) :
    (mixedRadialJacobian K y : ℂ) *
        mixedMellinGaussian K x s (expMapBasis y) =
      (((2 : ℝ)⁻¹ ^ nrComplexPlaces K *
          (Module.finrank ℚ K : ℝ) * regulator K : ℝ) : ℂ) *
        Complex.exp ((Module.finrank ℚ K : ℂ) * s *
          (y Units.dirichletUnitTheorem.w₀ : ℂ)) *
        mixedGaussian K x (expMapBasis y) := by
  have hp : (∏ v : InfinitePlace K, (expMapBasis y v : ℂ)) *
      (∏ v : InfinitePlace K, (expMapBasis y v : ℂ) ^ ((v.mult : ℂ) * s - 1)) =
      Complex.exp ((Module.finrank ℚ K : ℂ) * s *
        (y dirichletUnitTheorem.w₀ : ℂ)) := by
    rw [← Finset.prod_mul_distrib]
    have he : ∀ v : InfinitePlace K,
        (expMapBasis y v : ℂ) * (expMapBasis y v : ℂ) ^ ((v.mult : ℂ) * s - 1) =
        Complex.exp (((v.mult : ℂ) * (Real.log (expMapBasis y v) : ℂ)) * s) := by
      intro v
      have hn : (expMapBasis y v : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (expMapBasis_pos y v).ne'
      rw [Complex.cpow_sub _ _ hn, Complex.cpow_one, mul_div_cancel₀ _ hn,
        Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log (expMapBasis_pos y v).le]
      congr 1
      ring
    simp_rw [he]
    rw [← Complex.exp_sum]
    rw [← Finset.sum_mul]
    have hs : (∑ v : InfinitePlace K,
        (v.mult : ℂ) * (Real.log (expMapBasis y v) : ℂ)) =
        (Module.finrank ℚ K : ℂ) * (y dirichletUnitTheorem.w₀ : ℂ) := by
      exact_mod_cast weighted_log_sum K y
    rw [hs]
    congr 1
    ring
  have hg : (∏ v : InfinitePlace K,
      Complex.exp (-(Real.pi : ℂ) * (v.mult : ℂ) *
        (expMapBasis y v : ℂ) ^ 2 * (v x : ℂ) ^ 2)) =
      mixedGaussian K x (expMapBasis y) := by
    rw [← Complex.exp_sum]
    unfold mixedGaussian
    congr 1
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_natCast]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [radialJacobian_eq_prod, mixedMellinGaussian, Finset.prod_mul_distrib]
  push_cast
  rw [← mul_assoc, mul_right_comm (∏ v : InfinitePlace K, (expMapBasis y v : ℂ)),
    mul_assoc, hp, hg]
  ring

theorem norm_mixedMellinGaussian
    (x : K) (s : ℂ) (q : InfinitePlace K → ℝ) (hq : ∀ v, 0 < q v) :
    ‖mixedMellinGaussian K x s q‖ =
      ∏ v : InfinitePlace K,
        (q v) ^ ((v.mult : ℝ) * s.re - 1) *
          Real.exp (-Real.pi * (v.mult : ℝ) * (q v) ^ 2 * (v x) ^ 2) := by
  unfold mixedMellinGaussian
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro v hv
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hq v), Complex.norm_exp]
  congr 2 <;> simp [Complex.mul_re, ← Complex.ofReal_pow]

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
