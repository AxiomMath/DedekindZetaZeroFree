module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.WeightedCoefficients
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.FiniteSupportDigits
public import DedekindZetaZeroFree.CharacterSums.Gauss.Squarefree.PrincipalNormBound

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.CRTAbsoluteSeries
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {F : Type} [Field F] [NumberField F]

abbrev ExteriorIndex (A : SArithmeticData F) :=
  ExteriorSquarefreeIdeal A.cS × A.Exterior × A.Exterior × A.Exterior

private theorem generator_quotient_norm
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A) (I : A.Exterior) :
    (FiniteTransform.exteriorNorm A.R.toSubring (D.generator I) : ℝ) =
      A.exteriorNorm I := by
  change (Nat.card (A.R ⧸ Ideal.span {D.generator I}) : ℝ) = _
  rw [(D.generates I).2, A.exteriorResidue_card]
  rfl

private theorem product_quotient_norm
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) :
    (FiniteTransform.exteriorNorm A.R.toSubring (D.generator c.val * D.generator n ^ 3) : ℝ) =
      A.exteriorNorm c.val * A.exteriorNorm n ^ 3 := by
  let I := ExteriorIdealEuler.mul c.val (ExteriorIdealEuler.pow n 3)
  have he : Ideal.span {D.generator c.val * D.generator n ^ 3} = A.extendIdeal I := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
      (D.generates c.val).2, (D.generates n).2]
    change Ideal.map (algebraMap (𝓞 F) A.R) c.val.val *
      Ideal.map (algebraMap (𝓞 F) A.R) n.val ^ 3 =
      Ideal.map (algebraMap (𝓞 F) A.R) (c.val.val * n.val ^ 3)
    rw [Ideal.map_mul, Ideal.map_pow]
  change (Nat.card (A.R ⧸ Ideal.span {D.generator c.val * D.generator n ^ 3}) : ℝ) = _
  rw [he, A.exteriorResidue_card]
  change (Ideal.absNorm (c.val.val * n.val ^ 3) : ℝ) = _
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
  rfl

private theorem finiteCoefficient_bound
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces) (G : A.GaussCorrectionOutput σ η hS)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS G)
    (c : ExteriorSquarefreeIdeal A.cS) (n s : A.Exterior) (h : A.R) :
    ‖comparisonPoissonFiniteCoefficient F A D c n s h‖ ≤
      A.exteriorNorm s * (A.exteriorNorm c.val * A.exteriorNorm n ^ 3) := by
  let a := D.generator c.val * D.generator n ^ 3
  have ha : a ≠ 0 := mul_ne_zero (D.generates c.val).1 (pow_ne_zero _ (D.generates n).1)
  letI := D.finiteResidue (D.generator s) (D.generates s).1
  letI := D.finiteResidue a ha
  have hb := FiniteTransform.finiteCoefficient_norm_le A.R.toSubring
    (D.generator s) a h (D.character (D.generator s)) (D.character a)
    D.additiveCharacter (fun x => by rw [hD.additive_recipe]; exact Circle.norm_coe _)
  change ‖FiniteTransform.finiteCoefficient A.R.toSubring (D.generator s) a h
    (D.character (D.generator s)) (D.character a) D.additiveCharacter‖ ≤ _
  convert hb using 1
  rw [generator_quotient_norm A D s, product_quotient_norm A D c n]

private theorem realPower_norm (q : ℝ) (hq : 0 < q) (s : ℂ) :
    ‖comparisonRealPower q s‖ = q ^ s.re := by
  rw [comparisonRealPower, Complex.norm_exp, Real.rpow_def_of_pos hq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [mul_comm]

 def fixedMajorant (A : SArithmeticData F) (ξ w z : ℂ) (i : ExteriorIndex A) : ℝ :=
  A.exteriorNorm i.1.val ^ (1 / 2 - ξ.re) *
    (A.exteriorNorm i.2.1 ^ (2 - 3 * ξ.re) *
      (A.exteriorNorm i.2.2.1 ^ (1 - w.re) * A.exteriorNorm i.2.2.2 ^ (-6 * z.re)))

private theorem summand_bound
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces) (G : A.GaussCorrectionOutput σ η hS)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS G)
    (u : A.R) (ξ w z : ℂ) (i : ExteriorIndex A) :
    ‖comparisonEulerPoissonSummand F A D u ξ w z i.1 i.2.1 i.2.2.1 i.2.2.2‖ ≤
      fixedMajorant A ξ w z i := by
  have hg : ‖D.gammaTwo i.1‖ ≤ 1 := by
    rw [hD.gammaTwo_recipe]
    exact NormalizedProbe.PrincipalData.norm_idealGauss_le_one A σ hS _ _ _ _
  have ht : ‖D.theta (D.generator i.1.val * D.generator i.2.1 ^ 3)‖ = 1 := by
    rw [hD.theta_recipe _ (mul_ne_zero (D.generates _).1 (pow_ne_zero _ (D.generates _).1))]
    exact Circle.norm_coe _
  have hf := finiteCoefficient_bound A D σ η hS G hD i.1 i.2.1 i.2.2.1
    (u * D.generator i.2.2.2 ^ 6)
  have he1 : (-1 / 2 - ξ).re = -1 / 2 - ξ.re := by
    norm_num [Complex.sub_re, Complex.neg_re, Complex.div_re, Complex.normSq]
  have he2 : (-1 - 3 * ξ).re = -1 - 3 * ξ.re := by
    norm_num [Complex.sub_re, Complex.neg_re, Complex.mul_re]
  have he3 : (-w).re = -w.re := Complex.neg_re w
  have he4 : (-6 * z).re = -6 * z.re := by
    norm_num [Complex.neg_re, Complex.mul_re]
  unfold comparisonEulerPoissonSummand
  simp only [norm_mul, ht, mul_one, realPower_norm _ (A.exteriorNorm_pos _),
    he1, he2, he3, he4]
  calc
    _ ≤ 1 * (A.exteriorNorm i.2.2.1 * (A.exteriorNorm i.1.val * A.exteriorNorm i.2.1 ^ 3)) *
        A.exteriorNorm i.1.val ^ (-1 / 2 - ξ.re) *
        A.exteriorNorm i.2.1 ^ (-1 - 3 * ξ.re) *
        A.exteriorNorm i.2.2.1 ^ (-w.re) * A.exteriorNorm i.2.2.2 ^ (-6 * z.re) := by
      gcongr <;> exact (Real.rpow_pos_of_pos (A.exteriorNorm_pos _) _).le
    _ = fixedMajorant A ξ w z i := by
      unfold fixedMajorant
      rw [show 1 / 2 - ξ.re = 1 + (-1 / 2 - ξ.re) by ring,
        show 2 - 3 * ξ.re = (3 : ℝ) + (-1 - 3 * ξ.re) by ring,
        show 1 - w.re = 1 + (-w.re) by ring]
      rw [Real.rpow_add (A.exteriorNorm_pos _), Real.rpow_add (A.exteriorNorm_pos _),
        Real.rpow_add (A.exteriorNorm_pos _)]
      rw [Real.rpow_one, Real.rpow_one,
        show (A.exteriorNorm i.2.1) ^ (3 : ℝ) = (A.exteriorNorm i.2.1) ^ (3 : ℕ) from
          Real.rpow_natCast _ 3]
      ring

private theorem fixedMajorant_summable
    (A : SArithmeticData F) (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    Summable (fixedMajorant A ξ w z) := by
  have hc : Summable (fun c : ExteriorSquarefreeIdeal A.cS =>
      A.exteriorNorm c.val ^ (1 / 2 - ξ.re)) := by
    have H := (ProbeExteriorIdealCount.ideal_norm_summable F A.cS (ξ.re - 1 / 2)
      (by linarith)).subtype (fun c : A.Exterior => Squarefree c.val)
    change Summable (fun c : ExteriorSquarefreeIdeal A.cS =>
      A.exteriorNorm c.val ^ (-(ξ.re - 1 / 2))) at H
    convert H using 1
    ext c
    congr 1
    ring
  have hn : Summable (fun n : A.Exterior => A.exteriorNorm n ^ (2 - 3 * ξ.re)) := by
    convert ProbeExteriorIdealCount.ideal_norm_summable F A.cS (3 * ξ.re - 2)
      (by linarith) using 1
    ext n
    congr 1
    ring
  have hs : Summable (fun s : A.Exterior => A.exteriorNorm s ^ (1 - w.re)) := by
    convert ProbeExteriorIdealCount.ideal_norm_summable F A.cS (w.re - 1)
      (by linarith) using 1
    ext s
    congr 1
    ring
  have hr : Summable (fun r : A.Exterior => A.exteriorNorm r ^ (-6 * z.re)) := by
    convert ProbeExteriorIdealCount.ideal_norm_summable F A.cS (6 * z.re)
      (by linarith) using 1
    ext r
    congr 1
    ring
  have hnonneg : ∀ (I : A.Exterior) (t : ℝ), 0 ≤ A.exteriorNorm I ^ t :=
    fun I t => (Real.rpow_pos_of_pos (A.exteriorNorm_pos I) t).le
  have Hsr := hs.mul_of_nonneg hr (fun s => hnonneg s _) (fun r => hnonneg r _)
  have Hnsr := hn.mul_of_nonneg Hsr (fun n => hnonneg n _)
    (fun i => mul_nonneg (hnonneg i.1 _) (hnonneg i.2 _))
  exact hc.mul_of_nonneg Hnsr (fun c => hnonneg c.val _)
    (fun i => mul_nonneg (hnonneg i.1 _)
      (mul_nonneg (hnonneg i.2.1 _) (hnonneg i.2.2 _)))

section FixedFrequency

variable (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
variable (hCl : Subsingleton (ClassGroup A.R)) (σ : F →+* ℂ)
variable (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
variable (G : A.GaussCorrectionOutput σ η hS)
variable (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS G)
variable (Iu : A.Exterior) (u : A.R) (hu : A.Generates Iu u)
variable (hu_allowed : A.IsAllowed G.B (WeightedFiniteCoefficient.fieldUnit A u hu.1))
variable (hsixthfree : ∀ p : WeightedFiniteCoefficient.ExteriorPrime A,
  idealPrimeExponent p.val.asIdeal Iu.val ≤ 5)
variable (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re)

include hCl σ η hS G hD Iu hu hu_allowed hsixthfree hξ hw hz in

theorem weightedSummand_summable :
    Summable (fun i : ExteriorIndex A =>
      ‖comparisonEulerPoissonSummand F A D u ξ w z
        i.1 i.2.1 i.2.2.1 i.2.2.2‖) := by
  exact (fixedMajorant_summable A ξ w z hξ hw hz).of_nonneg_of_le
    (fun i => norm_nonneg _) (summand_bound A D σ η hS G hD u ξ w z)

end FixedFrequency

end
end DedekindZetaZeroFree.CRTAbsoluteSeries
