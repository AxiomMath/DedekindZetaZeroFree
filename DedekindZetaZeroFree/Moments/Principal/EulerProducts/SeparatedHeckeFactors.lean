module

public import DedekindZetaZeroFree.Arithmetic.Kummer.SexticFrequencyCharacters
public import DedekindZetaZeroFree.Moments.Principal.Corrections.NormalProductConvergence
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.CoefficientFactorization
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.PrimeFactorSeparation

@[expose] public section

open scoped NumberField Classical

noncomputable section
namespace DedekindZetaZeroFree.InitialSeparatedEuler
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CorrectionFactors FrequencyCharacterMasks

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}

def dirichletSeries (a : A.Exterior → ℂ) (s : ℂ) : ℂ :=
  ∑' I : A.Exterior, ExteriorIdealEuler.summand a s I

def plusL (U : Frequency C) (s : ℂ) : ℂ :=
  dirichletSeries (plusExteriorCoefficient U) s

def minusL (U : Frequency C) (s : ℂ) : ℂ :=
  dirichletSeries (minusExteriorCoefficient U) s

def zetaS (A : SArithmeticData F) (s : ℂ) : ℂ :=
  ∑' I : A.Exterior, (Ideal.absNorm I.val : ℂ) ^ (-s)

theorem correction_multipliable_initial (U : Frequency C)
    (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    Multipliable (fun p : LocalFiniteSums.ExteriorPrime A =>
      localFactor C U p ξ w z) := by
  apply multipliable_localFactor C U (ξ, w, z)
  apply Or.inl
  change _ ∧ _ ∧ _
  exact ⟨by linarith, by linarith, by linarith⟩

 def primeEquiv (A : SArithmeticData F) :
    LocalFiniteSums.ExteriorPrime A ≃ ExteriorIdealEuler.PrimeIndex A.cS where
  toFun p := ⟨LocalFiniteSums.primeIdeal p, p.val.prime⟩
  invFun p := ⟨⟨p.val.val, (Ideal.prime_iff_isPrime p.val.property.1).mp p.property,
    p.val.property.1⟩, p.val.property.2⟩
  left_inv p := by rfl
  right_inv p := by rfl

private lemma normPower_eq (p : LocalFiniteSums.ExteriorPrime A) (s : ℂ) :
    (Ideal.absNorm p.val.asIdeal : ℂ) ^ s = LocalFiniteSums.qPower p s := by
  have hn : (0 : ℝ) < (Ideal.absNorm p.val.asIdeal : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one
      (NumberField.HeightOneSpectrum.one_lt_absNorm p.val))
  have hne : (Ideal.absNorm p.val.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hn)
  rw [Complex.cpow_def_of_ne_zero hne]
  have hl : Complex.log (Ideal.absNorm p.val.asIdeal : ℂ) =
      (Real.log (Ideal.absNorm p.val.asIdeal : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hn.le).symm
  rw [hl]
  change Complex.exp _ = Complex.exp (s * _)
  congr 1
  simp only [LocalFiniteSums.Q, SArithmeticData.exteriorNorm, idealNorm,
    LocalFiniteSums.primeIdeal]
  ring

private lemma term_plus (U : Frequency C) (p : LocalFiniteSums.ExteriorPrime A)
    (s : ℂ) :
    ExteriorIdealEuler.primeTerm (plusExteriorCoefficient U) s (primeEquiv A p) =
      W (σ := σ) p U.u s := by
  change plusExteriorCoefficient U (LocalFiniteSums.primeIdeal p) *
    (Ideal.absNorm p.val.asIdeal : ℂ) ^ (-s) = _
  rw [normPower_eq]
  rfl

private lemma term_minus (U : Frequency C) (p : LocalFiniteSums.ExteriorPrime A)
    (s : ℂ) :
    ExteriorIdealEuler.primeTerm (minusExteriorCoefficient U) s (primeEquiv A p) =
      CorrectionFactors.D (σ := σ) (η := η) p U.u s := by
  change minusExteriorCoefficient U (LocalFiniteSums.primeIdeal p) *
    (Ideal.absNorm p.val.asIdeal : ℂ) ^ (-s) = _
  rw [normPower_eq]
  rfl

private lemma term_zeta (p : LocalFiniteSums.ExteriorPrime A) (z : ℂ) :
    ExteriorIdealEuler.primeTerm (fun _ : A.Exterior => (1 : ℂ)) (6 * z)
      (primeEquiv A p) = V p z := by
  change 1 * (Ideal.absNorm p.val.asIdeal : ℂ) ^ (-(6 * z)) = _
  rw [one_mul, normPower_eq]
  unfold V
  congr 1
  ring

theorem initial_separated_euler (U : Frequency C)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    minusL U ξ ≠ 0 ∧
      comparisonEulerPoissonSeries F A D U.u ξ w z * minusL U ξ =
        zetaS A (6 * z) * plusL U w *
          H_u C U ξ w z (correction_multipliable_initial U ξ w z hξ hw hz) := by
  have hc := actual_coefficients_multiplicative U
  have hξ1 : 1 < ξ.re := by linarith
  have hw1 : 1 < w.re := by linarith
  have hz1 : 1 < (6 * z).re := by simp; linarith
  have hm := ExteriorIdealEuler.exterior_ideal_euler _ hc.2.1 ξ hξ1
  have hp := ExteriorIdealEuler.exterior_ideal_euler _ hc.1 w hw1
  have hzeta := ExteriorIdealEuler.exterior_ideal_euler _
    (ExteriorIdealEuler.constant_one_isCoefficient A.cS) (6 * z) hz1
  have hne : minusL U ξ ≠ 0 := hm.2.2.1
  refine ⟨hne, ?_⟩
  have hDen : HasProd (fun p : LocalFiniteSums.ExteriorPrime A =>
      1 - CorrectionFactors.D (σ := σ) (η := η) p U.u ξ) (minusL U ξ)⁻¹ := by
    have h := (primeEquiv A).hasProd_iff.mpr hm.2.2.2
    simpa only [Function.comp_def, term_minus, minusL, dirichletSeries] using h
  have hW : HasProd (fun p : LocalFiniteSums.ExteriorPrime A =>
      (1 - W (σ := σ) p U.u w)⁻¹) (plusL U w) := by
    have h := (primeEquiv A).hasProd_iff.mpr hp.2.1
    simpa only [Function.comp_def, ExteriorIdealEuler.factor, term_plus, plusL, dirichletSeries] using h
  have hV : HasProd (fun p : LocalFiniteSums.ExteriorPrime A =>
      (1 - V p z)⁻¹) (zetaS A (6 * z)) := by
    have h := (primeEquiv A).hasProd_iff.mpr hzeta.2.1
    simpa only [Function.comp_def, ExteriorIdealEuler.factor, term_zeta,
      ExteriorIdealEuler.summand, one_mul, zetaS] using h
  have hH := (correction_multipliable_initial U ξ w z hξ hw hz).hasProd
  have hprod := ((hDen.mul hV).mul hW).mul hH
  have hlocal (p : LocalFiniteSums.ExteriorPrime A) :
      LocalFiniteSums.f C p (U.j p) (U.theta p) ξ w z =
      (1 - CorrectionFactors.D (σ := σ) (η := η) p U.u ξ) *
        (1 - V p z)⁻¹ * (1 - W (σ := σ) p U.u w)⁻¹ *
        localFactor C U p ξ w z := by
    obtain ⟨hv, hw'⟩ := prime_factor_separation_denominators_nonzero C U p ξ w z hξ hw hz
    have he := prime_factor_separation C U p ξ w z hξ hw hz
    apply (mul_left_cancel₀ (mul_ne_zero hv hw'))
    calc
      (1 - V p z) * (1 - W (σ := σ) p U.u w) *
          LocalFiniteSums.f C p (U.j p) (U.theta p) ξ w z =
          (1 - CorrectionFactors.D (σ := σ) (η := η) p U.u ξ) *
            localFactor C U p ξ w z := he
      _ = _ := by field_simp
  have hseries : HasProd (fun p : LocalFiniteSums.ExteriorPrime A =>
      LocalFiniteSums.f C p (U.j p) (U.theta p) ξ w z)
      (comparisonEulerPoissonSeries F A D U.u ξ w z) :=
    CRTEulerSeparation.hasProd_local_series U D hD ξ w z hξ hw hz
  have heq := hseries.unique (hprod.congr_fun hlocal)
  change comparisonEulerPoissonSeries F A D U.u ξ w z * minusL U ξ = _
  rw [heq]
  change (minusL U ξ)⁻¹ * zetaS A (6 * z) * plusL U w *
    H_u C U ξ w z (correction_multipliable_initial U ξ w z hξ hw hz) * minusL U ξ = _
  field_simp

theorem initial_separated_euler_quotient (U : Frequency C)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    comparisonEulerPoissonSeries F A D U.u ξ w z =
      zetaS A (6 * z) * plusL U w *
        H_u C U ξ w z (correction_multipliable_initial U ξ w z hξ hw hz) /
          minusL U ξ := by
  obtain ⟨hne, heq⟩ := initial_separated_euler U D hD ξ w z hξ hw hz
  exact (eq_div_iff hne).mpr heq

end DedekindZetaZeroFree.InitialSeparatedEuler

end
