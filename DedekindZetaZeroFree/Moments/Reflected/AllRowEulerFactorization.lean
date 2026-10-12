module

public import DedekindZetaZeroFree.Theta.Whittaker.LocalEuler.InitialBoundary
public import DedekindZetaZeroFree.Theta.Whittaker.LocalEuler.UnitCovariance
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.SeparatedHeckeFactors

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.AllRowEuler.InitialSeparation
open LocalFiniteSums

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}

structure RawFrequency (A : SArithmeticData F) where
  u : A.R
  ideal : A.Exterior
  generates : A.Generates ideal u
  sixthFree : ∀ p : ExteriorPrime A, idealPrimeExponent p.val.asIdeal ideal.val < 6

namespace RawFrequency

def j (U : RawFrequency A) (p : ExteriorPrime A) : Fin 6 :=
  ⟨idealPrimeExponent p.val.asIdeal U.ideal.val, U.sixthFree p⟩

theorem exists_unitPart (C : A.GeneralArithmeticContext σ η hS)
    (U : RawFrequency A) (p : ExteriorPrime A) :
    ∃ v : A.R, U.u = generator C p ^ (U.j p).val * v ∧
      IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) v) := by

  obtain ⟨r, a, hr, har, ha⟩ := C.allowed_integral U.ideal
  have hrAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (r : F) (by exact_mod_cast hr.1)) := by
    convert ha using 1
    apply Units.ext
    exact har.symm
  let V : CorrectionFactors.Frequency C := ⟨r, U.ideal, hr, hrAllowed, U.sixthFree⟩

  have hassoc : Associated r U.u := Ideal.span_singleton_eq_span_singleton.mp
    (hr.2.trans U.generates.2.symm)
  obtain ⟨eps, heps⟩ := hassoc
  obtain ⟨v, hv, hvUnit⟩ := V.exists_unitPart p
  change r = generator C p ^ (U.j p).val * v at hv
  refine ⟨(eps : A.R) * v, ?_, ?_⟩
  · rw [← heps, hv]
    ring
  · rw [map_mul]
    exact (eps.isUnit.map _).mul hvUnit

def unitPart (C : A.GeneralArithmeticContext σ η hS)
    (U : RawFrequency A) (p : ExteriorPrime A) : A.R :=
  Classical.choose (U.exists_unitPart C p)

theorem unitPart_spec (C : A.GeneralArithmeticContext σ η hS)
    (U : RawFrequency A) (p : ExteriorPrime A) :
    U.u = generator C p ^ (U.j p).val * U.unitPart C p ∧
      IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (U.unitPart C p)) :=
  Classical.choose_spec (U.exists_unitPart C p)

def theta (C : A.GeneralArithmeticContext σ η hS)
    (U : RawFrequency A) (p : ExteriorPrime A) : {θ : ℂ // ‖θ‖ = 1} :=
  ⟨UnitCovariance.residueCoefficient σ (primeIdeal p) (U.unitPart C p),
    UnitCovariance.residueCoefficient_norm_of_isUnit _ _ (U.unitPart_spec C p).2⟩

end RawFrequency

def plusExteriorCoefficient (σ : F →+* ℂ) (U : RawFrequency A) (I : A.Exterior) : ℂ :=
  UnitCovariance.residueCoefficient σ I U.u

def minusExteriorCoefficient (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (U : RawFrequency A) (I : A.Exterior) : ℂ :=
  η I.val * star (plusExteriorCoefficient σ U I)

def plusL (σ : F →+* ℂ) (U : RawFrequency A) (s : ℂ) : ℂ :=
  InitialSeparatedEuler.dirichletSeries (plusExteriorCoefficient σ U) s

def minusL (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (U : RawFrequency A) (s : ℂ) : ℂ :=
  InitialSeparatedEuler.dirichletSeries (minusExteriorCoefficient σ η U) s

def localCorrection (C : A.GeneralArithmeticContext σ η hS)
    (U : RawFrequency A) (p : ExteriorPrime A) (ξ w z : ℂ) : ℂ :=
  if (U.j p).val = 0 then CorrectionFactors.goodFactor C p U.u ξ w z
  else CorrectionFactors.badFactor C p (U.j p) (U.theta C p) ξ w z

def correctionProduct (C : A.GeneralArithmeticContext σ η hS)
    (U : RawFrequency A) (ξ w z : ℂ) : ℂ :=
  ∏' p : ExteriorPrime A, localCorrection C U p ξ w z

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

 def fixedMajorant (A : SArithmeticData F) (ξ w z : ℂ)
    (i : CRTAbsoluteSeries.ExteriorIndex A) : ℝ :=
  A.exteriorNorm i.1.val ^ (1 / 2 - ξ.re) *
    (A.exteriorNorm i.2.1 ^ (2 - 3 * ξ.re) *
      (A.exteriorNorm i.2.2.1 ^ (1 - w.re) * A.exteriorNorm i.2.2.2 ^ (-6 * z.re)))

private theorem summand_bound
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces) (G : A.GaussCorrectionOutput σ η hS)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS G)
    (u : A.R) (ξ w z : ℂ) (i : CRTAbsoluteSeries.ExteriorIndex A) :
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
    (A : SArithmeticData F) (ξ w z : ℂ)
    (hξ : 3 / 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
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

theorem comparisonSeries_summable
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces) (G : A.GaussCorrectionOutput σ η hS)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS G)
    (u : A.R) (ξ w z : ℂ)
    (hξ : 3 / 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
    Summable (fun i : CRTAbsoluteSeries.ExteriorIndex A =>
      ‖comparisonEulerPoissonSummand F A D u ξ w z
        i.1 i.2.1 i.2.2.1 i.2.2.2‖) :=
  (fixedMajorant_summable A ξ w z hξ hw hz).of_nonneg_of_le
    (fun i => norm_nonneg _) (summand_bound A D σ η hS G hD u ξ w z)

private lemma plus_base_raw (U : RawFrequency A) (I : A.Exterior) :
    plusExteriorCoefficient σ U I = σ (A.sexticResidue I U.u) :=
  UnitCovariance.residueCoefficient_eq I U.u

private lemma plus_ext_mul_raw (U : RawFrequency A) (I J : A.Exterior) :
    plusExteriorCoefficient σ U (ExteriorIdealEuler.mul I J) =
      plusExteriorCoefficient σ U I * plusExteriorCoefficient σ U J := by
  simp only [plus_base_raw]
  rw [show A.sexticResidue (ExteriorIdealEuler.mul I J) U.u =
    A.sexticResidue I U.u * A.sexticResidue J U.u from
      A.sexticResidueFamily_normalized.2.2 I J _ rfl U.u, map_mul]

private lemma plus_ext_one_raw (U : RawFrequency A) :
    plusExteriorCoefficient σ U (ExteriorIdealEuler.one A.cS) = 1 := by
  rw [plus_base_raw]
  rw [show A.sexticResidue (ExteriorIdealEuler.one A.cS) U.u = 1 from
    A.residueValue_top _ _ rfl _, map_one]

private lemma plus_ext_norm_raw (U : RawFrequency A) (I : A.Exterior) :
    ‖plusExteriorCoefficient σ U I‖ ≤ 1 := by
  rw [plus_base_raw]
  by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) U.u)
  · change ‖σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)‖ ≤ 1
    rw [← hx.unit_spec, MulChar.ofUnitHom_coe]
    have hp := A.sexticResidueFamily_normalized.1 I hx.unit
    have hp' : σ ((A.sexticResidueFamily I hx.unit : Fˣ) : F) ^ 6 = 1 := by
      rw [← map_pow]
      simpa using congrArg (fun u : Fˣ => σ (u : F)) hp
    exact (Complex.norm_eq_one_of_pow_eq_one hp' (by decide)).le
  · change ‖σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)‖ ≤ 1
    rw [MulChar.map_nonunit _ hx, map_zero, norm_zero]
    exact zero_le_one

private lemma plus_ext_pow_raw (U : RawFrequency A) (I : A.Exterior) (k : ℕ) :
    plusExteriorCoefficient σ U (ExteriorIdealEuler.pow I k) =
      plusExteriorCoefficient σ U I ^ k := by
  induction k with
  | zero => simpa [ExteriorIdealEuler.pow, ExteriorIdealEuler.one] using plus_ext_one_raw (σ := σ) U
  | succ k ih =>
    have he : ExteriorIdealEuler.pow I (k+1) =
        ExteriorIdealEuler.mul (ExteriorIdealEuler.pow I k) I := by
      apply Subtype.ext; simp [ExteriorIdealEuler.pow, ExteriorIdealEuler.mul, pow_succ]
    rw [he, plus_ext_mul_raw, ih, pow_succ]

theorem raw_plus_isCoefficient (U : RawFrequency A) :
    ExteriorIdealEuler.IsCoefficient (plusExteriorCoefficient σ U) :=
  ⟨plus_ext_one_raw U, fun I J _ => plus_ext_mul_raw U I J,
    plus_ext_norm_raw U, fun p k => plus_ext_pow_raw U p.val k⟩

theorem raw_minus_isCoefficient (U : RawFrequency A) :
    ExteriorIdealEuler.IsCoefficient (minusExteriorCoefficient σ η U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [minusExteriorCoefficient, plus_ext_one_raw]
    simp [ExteriorIdealEuler.one, RayClassCharacter.map_top']
  · intro I J h
    rw [minusExteriorCoefficient, plus_ext_mul_raw]
    simp only [minusExteriorCoefficient, ExteriorIdealEuler.mul, RayClassCharacter.map_mul',
      star_mul]
    ring
  · intro I
    rw [minusExteriorCoefficient, norm_mul, norm_star]
    exact mul_le_one₀ (RayUnitary.ray_character_norm_le_one F A.modulus A.modulus_ne_zero η I.val)
      (norm_nonneg _) (plus_ext_norm_raw U I)
  · intro p k
    have hη : η (p.val.val ^ k) = η p.val.val ^ k := by
      induction k with
      | zero => simp [RayClassCharacter.map_top']
      | succ k ih => rw [pow_succ, RayClassCharacter.map_mul', ih, pow_succ]
    rw [minusExteriorCoefficient, plus_ext_pow_raw]
    simp only [minusExteriorCoefficient, ExteriorIdealEuler.pow, hη, star_pow, mul_pow]

theorem raw_minusL_ne_zero (U : RawFrequency A) (s : ℂ) (hs : 1 < s.re) :
    minusL σ η U s ≠ 0 := by
  have h := (ExteriorIdealEuler.exterior_ideal_euler (minusExteriorCoefficient σ η U)
    (raw_minus_isCoefficient U) s hs).2.2.1
  simpa [minusL, InitialSeparatedEuler.dirichletSeries] using h

private theorem raw_good_cofinite (U : RawFrequency A) :
    ∀ᶠ p : ExteriorPrime A in Filter.cofinite, (U.j p).val = 0 := by
  apply Filter.eventually_cofinite.mpr
  have hinj : Function.Injective (fun p : ExteriorPrime A => p.val.asIdeal) :=
    IsDedekindDomain.HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective
  simpa [RawFrequency.j, idealPrimeExponent, Multiset.count_eq_zero] using
    (UniqueFactorizationMonoid.normalizedFactors U.ideal.val).finite_toSet.preimage
      hinj.injOn

private theorem raw_good_unit (C : A.GeneralArithmeticContext σ η hS)
    (U : RawFrequency A) (p : ExteriorPrime A) (hp : (U.j p).val = 0) :
    IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) := by
  have hs := U.unitPart_spec C p
  rw [hs.1, hp, pow_zero, one_mul]
  exact hs.2

private theorem raw_correction_majorant_summable (M : ℝ) :
    Summable (fun p : ExteriorPrime A =>
      M * (Q p) ^ (-(1 + 1 / 4000 : ℝ))) := by
  let i : ExteriorPrime A → {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // p ∉ A.Sf} :=
    fun p => ⟨p.val, by
      intro hp
      have he := (A.exterior_iff ⟨p.val.asIdeal, p.val.ne_bot⟩).mp p.property p.val hp
      simp only [sup_idem] at he
      exact p.val.isPrime.ne_top he⟩
  have hi : Function.Injective i := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun r : {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // p ∉ A.Sf} => r.val) h
  have hs := (summable_exterior_prime_norm_rpow F A.Sf (1 + 1 / 4000) (by norm_num)).comp_injective hi
  simpa [Function.comp_def, i, Q, SArithmeticData.exteriorNorm, idealNorm, primeIdeal]
    using hs.mul_left M

theorem raw_correction_deviations_summable
    (C : A.GeneralArithmeticContext σ η hS) (U : RawFrequency A)
    (x : CorrectionFactors.Coordinates) (hx : x ∈ CorrectionFactors.Omega) :
    Summable (fun p : ExteriorPrime A =>
      ‖localCorrection C U p x.1 x.2.1 x.2.2 - 1‖) := by
  obtain ⟨M, hM, hbound⟩ := CorrectionFactors.good_correction_uniform_bound
  apply (raw_correction_majorant_summable (A := A) M).of_norm_bounded_eventually
  filter_upwards [raw_good_cofinite U] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simpa [localCorrection, hp] using
    hbound F A σ η hS C p U.u (raw_good_unit C U p hp) x hx

theorem raw_correction_multipliable
    (C : A.GeneralArithmeticContext σ η hS) (U : RawFrequency A)
    (x : CorrectionFactors.Coordinates) (hx : x ∈ CorrectionFactors.Omega) :
    Multipliable (fun p : ExteriorPrime A =>
      localCorrection C U p x.1 x.2.1 x.2.2) := by
  simpa only [add_sub_cancel] using
    multipliable_one_add_of_summable (raw_correction_deviations_summable C U x hx)

namespace RawCRT
open IsDedekindDomain CorrectionFactors
set_option autoImplicit false

open GlobalPairCancel

private theorem raw_global_pair_cancel
    (A : SArithmeticData F) (hCl : Subsingleton (ClassGroup A.R)) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (G : A.GaussCorrectionOutput σ η hS)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : HasArithmeticRecipes A σ hS G.B D)
    (c : ExteriorSquarefreeIdeal A.cS) (n s r Iu : A.Exterior)
    (u : A.R) (hu : A.Generates Iu u)
    (huSixthFree : ∀ v : HeightOneSpectrum (𝓞 F),
      idealPrimeExponent v.asIdeal Iu.val ≤ 5)
    (P : Finset (HeightOneSpectrum (𝓞 F)))
    (p : P → A.Exterior) (hp : ∀ v : P, (p v).val = v.val.asIdeal)
    (π : P → A.R) (hπ : ∀ v : P, A.Generates (p v) (π v))
    (aπ : P → Fˣ) (haπ : ∀ v : P, (aπ v : F) = (π v : F))
    (hπAllowed : ∀ v : P, A.IsAllowed G.B (aπ v))
    (hSupport : ∀ I ∈ ({c.val, n, s, r, Iu} : Finset A.Exterior),
      I.val = ∏ v : P, v.val.asIdeal ^ idealPrimeExponent v.val.asIdeal I.val)
    (uPrimeFree : P → A.R)
    (hPrimeFree : ∀ v : P,
      u = π v ^ idealPrimeExponent v.val.asIdeal Iu.val * uPrimeFree v)
    (hPrimeUnit : ∀ v : P,
      IsUnit (Ideal.Quotient.mk (A.extendIdeal (p v)) (uPrimeFree v))) :
    (∀ v : P, frequencyTheta A σ (p v) (uPrimeFree v) ≠ 0 ∧
      frequencyTheta A σ (p v) (uPrimeFree v) ^ 6 = 1) ∧
    D.gammaTwo c * comparisonPoissonFiniteCoefficient F A D c n s
        (u * D.generator r ^ 6) =
      ∏ v : P,
        let e := idealPrimeExponent v.val.asIdeal c.val.val
        let l := idealPrimeExponent v.val.asIdeal n.val
        let t := e + 3 * l
        let k := idealPrimeExponent v.val.asIdeal s.val
        let j := idealPrimeExponent v.val.asIdeal Iu.val
        let m := idealPrimeExponent v.val.asIdeal r.val
        A.idealGauss σ hS (p v) (π v) (hπ v) 2 ^ e *
          frequencyTheta A σ (p v) (uPrimeFree v) ^ ((k : ℤ) - (t : ℤ)) *
          primePowerSum A D (π v) (hπ v).1 t k (j + 6 * m) := by
  refine ⟨fun v => frequencyTheta_unit A σ (p v) (uPrimeFree v) (hPrimeUnit v), ?_⟩
  classical

  letI : LinearOrder P := LinearOrder.lift' (Fintype.equivFin P)
    (Fintype.equivFin P).injective
  letI : LocallyFiniteOrderTop P := LocallyFiniteOrderTop.ofIci P
    (fun v => Finset.univ.filter (fun w => v ≤ w)) (by simp)
  letI : LocallyFiniteOrderBot P := LocallyFiniteOrderBot.ofIic P
    (fun v => Finset.univ.filter (fun w => w ≤ v)) (by simp)
  have hReplace := GaussProductCancellation.prime_product_replacement
    A hCl σ η hS G D (hD.compatible A σ hS G.B D) hD.1 c n s r u
    P p hp π hπ aπ haπ hπAllowed (by
      intro I hI
      apply hSupport I
      simp only [Finset.mem_insert, Finset.mem_singleton] at hI ⊢
      rcases hI with hI | hI | hI | hI <;> simp [hI])
  have hRaw := GaussProductCancellation.masked_product_assembly A σ η hS G D
    hD.2.1 hD.2.2.1 c.val n s r Iu u hu P p hp π hπ aπ haπ hπAllowed
    hSupport uPrimeFree hPrimeFree hPrimeUnit
  obtain ⟨ac, hac, hcAllowed⟩ := hD.1 c.val
  have hGauss := GaussProductCancellation.gauss_product_assembly
    A hCl σ η hS G c (D.generator c.val) (D.generates c.val)
    ac hac hcAllowed P p hp π hπ aπ haπ hπAllowed
    (hSupport c.val (by simp))
  have hcop : ∀ v w : P, v ≠ w → (p v).val ⊔ (p w).val = ⊤ := by
    intro v w hvw
    rw [hp v, hp w]
    exact Ideal.isCoprime_iff_sup_eq.mp
      (HeightOneSpectrum.isCoprime_of_ne v.val w.val
        (fun h => hvw (Subtype.ext h)))
  have hCancel := actual_cross_prime_product_cancel A σ η hS G p π hπ
    aπ haπ hπAllowed hcop
    (fun v => idealPrimeExponent v.val.asIdeal c.val.val)
    (fun v => idealPrimeExponent v.val.asIdeal n.val)
    (fun v => idealPrimeExponent v.val.asIdeal s.val)
  rw [hD.2.2.2 c, hGauss, hReplace, hRaw]
  dsimp only at hCancel ⊢
  simp only [frequencyTheta, primePowerSum]
  rw [mul_mul_mul_comm]
  have hCancel' :
      (∏ v : P, ∏ w ∈ Finset.Ioi v,
        σ (A.sexticResidue (p v) (π w)) ^
          (4 * idealPrimeExponent v.val.asIdeal c.val.val *
            idealPrimeExponent w.val.asIdeal c.val.val)) *
      (∏ v : P, ∏ w ∈ ({v}ᶜ : Finset P),
        σ (A.sexticResidue (p v) (π w)) ^
          (((idealPrimeExponent v.val.asIdeal c.val.val +
              3 * idealPrimeExponent v.val.asIdeal n.val : ℕ) : ℤ) *
              idealPrimeExponent w.val.asIdeal s.val +
            (((idealPrimeExponent v.val.asIdeal c.val.val +
                3 * idealPrimeExponent v.val.asIdeal n.val : ℕ) : ℤ) -
                idealPrimeExponent v.val.asIdeal s.val) *
              (idealPrimeExponent w.val.asIdeal c.val.val +
                3 * idealPrimeExponent w.val.asIdeal n.val))) = 1 := by
    convert hCancel using 1
    congr 1
    apply Finset.prod_congr rfl
    intro v _
    apply Finset.prod_congr
    · ext w
      simp only [Finset.mem_compl, Finset.mem_singleton]
    · intro w _
      rfl
  rw [hCancel', mul_one, ← Finset.prod_mul_distrib]
  simp only [mul_assoc]

def localCoefficient (C : A.GeneralArithmeticContext σ η hS) (U : RawFrequency A)
    (p : ExteriorPrime A) (e l k m : ℕ) : ℂ :=
  gammaTwo C p ^ e * vartheta C p ^ (e + 3 * l) *
    (U.theta C p).val ^ ((k : ℤ) - (e : ℤ) - 3 * (l : ℤ)) *
    Ctk C p (e + 3 * l) k ((U.j p).val + 6 * m)

private theorem power_generates (p : ExteriorPrime A) (n : ℕ) :
    A.Generates (powerIdeal p n) (generator C p ^ n) := by
  refine ⟨pow_ne_zero _ (generator_generates C p).1, ?_⟩
  rw [← Ideal.span_singleton_pow, (generator_generates C p).2]
  exact (Ideal.map_pow _ _ _).symm
private theorem exponent_power (p q : ExteriorPrime A) (n : ℕ) :
    idealPrimeExponent q.val.asIdeal (powerIdeal p n).val = if q = p then n else 0 := by
  change (UniqueFactorizationMonoid.normalizedFactors (p.val.asIdeal ^ n)).count q.val.asIdeal = _
  rw [UniqueFactorizationMonoid.normalizedFactors_pow]
  simp only [UniqueFactorizationMonoid.normalizedFactors_irreducible p.val.irreducible,
    Multiset.count_nsmul, Multiset.count_singleton]
  by_cases h : q = p
  · simp [h]
  · have h' : q.val.asIdeal ≠ p.val.asIdeal := fun hh => h (Subtype.ext (HeightOneSpectrum.asIdeal_injective hh))
    simp [h, h', Ne.symm h']
private theorem power_allowed (p : ExteriorPrime A) (n : ℕ) :
    A.IsAllowed C.correction.B
      (WeightedFiniteCoefficient.fieldUnit A (generator C p ^ n) (power_generates p n).1) := by
  have he : WeightedFiniteCoefficient.fieldUnit A (generator C p ^ n) (power_generates p n).1 =
      WeightedFiniteCoefficient.fieldUnit A (generator C p) (generator_generates C p).1 ^ n := by
    apply Units.ext
    simp [WeightedFiniteCoefficient.fieldUnit]
  rw [he, SArithmeticData.IsAllowed, map_pow]
  exact C.correction.B.pow_mem (generator_allowed C p) n
private theorem local_unit_one (p : ExteriorPrime A) (n : ℕ) :
    MaskedQuotientCRT.localUnitPart C p (powerIdeal p n) (generator C p ^ n)
      (power_generates p n) = 1 := by
  apply Units.ext
  apply Subtype.ext
  rw [MaskedQuotientCRT.localUnitPart_spec]
  have hπ : (generator C p : F) ≠ 0 := by exact_mod_cast (generator_generates C p).1
  have hu : uniformizer C p ≠ 0 := (map_ne_zero (algebraMap F (LocalField p))).mpr hπ
  have hu' : algebraMap F (LocalField p) (generator C p : F) ≠ 0 := hu
  simp [MaskedQuotientCRT.primeExponent, exponent_power, uniformizer, map_pow, hπ, hu']
private theorem prime_sum_eq (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (p : ExteriorPrime A) (t k J : ℕ) :
    GlobalPairCancel.primePowerSum A D (generator C p) (generator_generates C p).1 t k J =
      Ctk C p t k J := by
  have hrec : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B D := by
    exact ⟨fun I => ⟨WeightedFiniteCoefficient.fieldUnit A _ (D.generates I).1,
      rfl, hD.generator_allowed I⟩, hD.character_recipe, hD.additive_recipe, hD.gammaTwo_recipe⟩
  have hc := hrec.coefficient_prime_power_crt A σ η hS C.correction.B D C
    (powerIdeal p k) (powerIdeal p t) (powerIdeal p J)
    (generator C p ^ k) (generator C p ^ t) (generator C p ^ J)
    (power_generates p k) (power_generates p t) (power_generates p J)
    (power_allowed p k) (power_allowed p t) {p}
    (fun q hq => by
      simp only [MaskedQuotientCRT.primeExponent, exponent_power, ne_eq,
        Finset.mem_singleton] at hq ⊢
      split_ifs at hq with h <;> simp_all)
    (fun q hq => by
      simp only [MaskedQuotientCRT.primeExponent, exponent_power, ne_eq,
        Finset.mem_singleton] at hq ⊢
      split_ifs at hq with h <;> simp_all)
    (fun q hq => by
      simp only [MaskedQuotientCRT.primeExponent, exponent_power, ne_eq,
        Finset.mem_singleton] at hq ⊢
      split_ifs at hq with h <;> simp_all)
  simpa [GlobalPairCancel.primePowerSum, MaskedQuotientCRT.primeExponent,
    exponent_power, local_unit_one, CompatiblePrimeRawLocal.R_one_eq_Ctk] using hc
private theorem theta_prime (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (p : ExteriorPrime A) : D.theta (D.generator (primeIdeal p)) = vartheta C p := by
  rw [hD.theta_recipe _ (D.generates _).1]
  change WeightedFiniteCoefficient.Proof.thetaHom A
    (A.correctionTheta C.correction.Λ C.correction.G C.correction.η_id)
    (WeightedFiniteCoefficient.fieldUnit A _ _) = _
  rw [WeightedFiniteCoefficient.Proof.theta_associated A _ C.correction.theta_unit
    _ _ (D.generates _).1 (generator_generates C p).1
    ((D.generates _).2.trans (generator_generates C p).2.symm)]
  rfl
private theorem theta_split (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (c n : A.Exterior) (P : Finset (ExteriorPrime A))
    (hc : ∀ p, p ∉ P → idealPrimeExponent p.val.asIdeal c.val = 0)
    (hn : ∀ p, p ∉ P → idealPrimeExponent p.val.asIdeal n.val = 0) :
    D.theta (D.generator c * D.generator n ^ 3) = ∏ p ∈ P,
      vartheta C p ^ (idealPrimeExponent p.val.asIdeal c.val +
        3 * idealPrimeExponent p.val.asIdeal n.val) := by
  have ht : D.theta (D.generator c * D.generator n ^ 3) =
      D.theta (D.generator c) * D.theta (D.generator n) ^ 3 := by
    rw [hD.theta_recipe _ (mul_ne_zero (D.generates _).1 (pow_ne_zero _ (D.generates _).1)),
      hD.theta_recipe _ (D.generates _).1, hD.theta_recipe _ (D.generates _).1]
    change WeightedFiniteCoefficient.Proof.thetaHom A _ (WeightedFiniteCoefficient.fieldUnit A _ _) =
      WeightedFiniteCoefficient.Proof.thetaHom A _ (WeightedFiniteCoefficient.fieldUnit A _ _) *
        WeightedFiniteCoefficient.Proof.thetaHom A _ (WeightedFiniteCoefficient.fieldUnit A _ _) ^ 3
    rw [WeightedFiniteCoefficient.Proof.fieldUnit_mul A _ _ (D.generates c).1
      (pow_ne_zero _ (D.generates n).1), map_mul]
    congr 1
    have he : WeightedFiniteCoefficient.fieldUnit A (D.generator n ^ 3)
        (pow_ne_zero _ (D.generates n).1) =
        WeightedFiniteCoefficient.fieldUnit A (D.generator n) (D.generates _).1 ^ 3 := by
      apply Units.ext
      simp [WeightedFiniteCoefficient.fieldUnit]
    rw [he, map_pow]
  rw [ht, WeightedFiniteCoefficient.Proof.theta_factor A D σ η hS C.correction hD c P
    (WeightedFiniteCoefficient.Proof.support_factor A c P hc),
    WeightedFiniteCoefficient.Proof.theta_factor A D σ η hS C.correction hD n P
    (WeightedFiniteCoefficient.Proof.support_factor A n P hn),
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  change D.theta (D.generator (primeIdeal p)) ^ _ *
    (D.theta (D.generator (primeIdeal p)) ^ _) ^ 3 = _
  rw [theta_prime D hD p, ← pow_mul, ← pow_add, Nat.mul_comm]

private theorem phase_eq (U : RawFrequency A) (p : ExteriorPrime A) :
    (U.theta C p).val = GlobalPairCancel.frequencyTheta A σ (primeIdeal p) (U.unitPart C p) := by
  exact UnitCovariance.residueCoefficient_eq _ _

theorem finite_coefficient_factorization (U : RawFrequency A)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (c : ExteriorSquarefreeIdeal A.cS) (n s r : A.Exterior)
    (P : Finset (ExteriorPrime A))
    (hsupport : ∀ p : ExteriorPrime A, p ∉ P →
      idealPrimeExponent p.val.asIdeal c.val.val = 0 ∧
      idealPrimeExponent p.val.asIdeal n.val = 0 ∧
      idealPrimeExponent p.val.asIdeal s.val = 0 ∧
      idealPrimeExponent p.val.asIdeal r.val = 0 ∧
      idealPrimeExponent p.val.asIdeal U.ideal.val = 0) :
    D.gammaTwo c * D.theta (D.generator c.val * D.generator n ^ 3) *
      comparisonPoissonFiniteCoefficient F A D c n s (U.u * D.generator r ^ 6) =
        ∏ p ∈ P, localCoefficient C U p
          (idealPrimeExponent p.val.asIdeal c.val.val)
          (idealPrimeExponent p.val.asIdeal n.val)
          (idealPrimeExponent p.val.asIdeal s.val)
          (idealPrimeExponent p.val.asIdeal r.val) := by
  let emb : ExteriorPrime A ↪ HeightOneSpectrum (𝓞 F) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let Q := P.map emb
  let E : P ≃ Q := Finset.equivMap emb P
  let ep : Q → ExteriorPrime A := fun v => (E.symm v).val
  have hep : ∀ v : Q, (ep v).val = v.val := by
    intro v
    exact congrArg Subtype.val (E.apply_symm_apply v)
  have hrec : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B D := by
    exact ⟨fun I => ⟨WeightedFiniteCoefficient.fieldUnit A _ (D.generates I).1,
      rfl, hD.generator_allowed I⟩, hD.character_recipe, hD.additive_recipe, hD.gammaTwo_recipe⟩
  have hfac : ∀ I ∈ ({c.val, n, s, r, U.ideal} : Finset A.Exterior),
      I.val = ∏ v : Q, v.val.asIdeal ^ idealPrimeExponent v.val.asIdeal I.val := by
    intro I hI
    have hs : ∀ p : ExteriorPrime A, p ∉ P → idealPrimeExponent p.val.asIdeal I.val = 0 := by
      intro p hp
      have ht := hsupport p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hI
      rcases hI with rfl | rfl | rfl | rfl | rfl
      · exact ht.1
      · exact ht.2.1
      · exact ht.2.2.1
      · exact ht.2.2.2.1
      · exact ht.2.2.2.2
    have hr := WeightedFiniteCoefficient.Proof.support_factor A I P hs
    refine hr.trans ?_
    rw [← Finset.prod_coe_sort]
    apply Fintype.prod_equiv E
    intro v
    rfl
  have hsix : ∀ v : HeightOneSpectrum (𝓞 F), idealPrimeExponent v.asIdeal U.ideal.val ≤ 5 := by
    intro v
    by_cases hz : idealPrimeExponent v.asIdeal U.ideal.val = 0
    · simp [hz]
    · have hd : v.asIdeal ∣ U.ideal.val := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
        (Multiset.count_ne_zero.mp hz)
      have hv : v.asIdeal ⊔ A.cS = ⊤ := by
        apply top_unique
        rw [← U.ideal.property.2]
        exact sup_le_sup_right (Ideal.dvd_iff_le.mp hd) _
      have hh : idealPrimeExponent v.asIdeal U.ideal.val < 6 := U.sixthFree ⟨v, hv⟩
      omega
  have hraw := (raw_global_pair_cancel A C.classGroup_trivial σ η hS C.correction D hrec
    c n s r U.ideal U.u U.generates hsix Q
    (fun v => primeIdeal (ep v)) (fun v => congrArg HeightOneSpectrum.asIdeal (hep v))
    (fun v => generator C (ep v)) (fun v => generator_generates C (ep v))
    (fun v => WeightedFiniteCoefficient.fieldUnit A _ (generator_generates C (ep v)).1)
    (fun v => rfl) (fun v => generator_allowed C (ep v)) hfac
    (fun v => U.unitPart C (ep v))
    (fun v => by simpa only [← hep v, RawFrequency.j] using (U.unitPart_spec C (ep v)).1)
    (fun v => (U.unitPart_spec C (ep v)).2)).2
  have hrawP : D.gammaTwo c * comparisonPoissonFiniteCoefficient F A D c n s
      (U.u * D.generator r ^ 6) = ∏ p ∈ P,
      gammaTwo C p ^ idealPrimeExponent p.val.asIdeal c.val.val *
      (U.theta C p).val ^ ((idealPrimeExponent p.val.asIdeal s.val : ℤ) -
        (idealPrimeExponent p.val.asIdeal c.val.val + 3 * idealPrimeExponent p.val.asIdeal n.val : ℕ)) *
      Ctk C p (idealPrimeExponent p.val.asIdeal c.val.val + 3 * idealPrimeExponent p.val.asIdeal n.val)
        (idealPrimeExponent p.val.asIdeal s.val)
        (idealPrimeExponent p.val.asIdeal U.ideal.val + 6 * idealPrimeExponent p.val.asIdeal r.val) := by
    refine hraw.trans ?_
    symm
    rw [← Finset.prod_coe_sort P]
    apply Fintype.prod_equiv E
    intro v
    dsimp only
    have hEv : (E v).val = v.val.val := by
      rw [← hep (E v)]
      simp [ep]
    simp only [hEv, ep, Equiv.symm_apply_apply, prime_sum_eq D hD, phase_eq U, gammaTwo]
  rw [show D.gammaTwo c * D.theta (D.generator c.val * D.generator n ^ 3) *
      comparisonPoissonFiniteCoefficient F A D c n s (U.u * D.generator r ^ 6) =
      (D.gammaTwo c * comparisonPoissonFiniteCoefficient F A D c n s (U.u * D.generator r ^ 6)) *
        D.theta (D.generator c.val * D.generator n ^ 3) by ring,
    hrawP, theta_split D hD c.val n P (fun p hp => (hsupport p hp).1)
      (fun p hp => (hsupport p hp).2.1), ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  unfold localCoefficient
  dsimp only [RawFrequency.j]
  rw [show (idealPrimeExponent p.val.asIdeal s.val : ℤ) -
      (idealPrimeExponent p.val.asIdeal c.val.val + 3 * idealPrimeExponent p.val.asIdeal n.val : ℕ) =
      (idealPrimeExponent p.val.asIdeal s.val : ℤ) -
        (idealPrimeExponent p.val.asIdeal c.val.val : ℤ) -
        3 * (idealPrimeExponent p.val.asIdeal n.val : ℤ) by push_cast; ring]
  ring

theorem norm_weights_factorization
    (c : ExteriorSquarefreeIdeal A.cS) (n s r : A.Exterior)
    (P : Finset (ExteriorPrime A))
    (hsupport : ∀ p : ExteriorPrime A, p ∉ P →
      idealPrimeExponent p.val.asIdeal c.val.val = 0 ∧
      idealPrimeExponent p.val.asIdeal n.val = 0 ∧
      idealPrimeExponent p.val.asIdeal s.val = 0 ∧
      idealPrimeExponent p.val.asIdeal r.val = 0)
    (ξ w z : ℂ) :
    comparisonRealPower (A.exteriorNorm c.val) (-1 / 2 - ξ) *
      comparisonRealPower (A.exteriorNorm n) (-1 - 3 * ξ) *
      comparisonRealPower (A.exteriorNorm s) (-w) *
      comparisonRealPower (A.exteriorNorm r) (-6 * z) =
        ∏ p ∈ P, qPower p
          (-(idealPrimeExponent p.val.asIdeal c.val.val : ℂ) * (1 / 2 + ξ) -
            (idealPrimeExponent p.val.asIdeal n.val : ℂ) * (1 + 3 * ξ) -
            (idealPrimeExponent p.val.asIdeal s.val : ℂ) * w -
            6 * (idealPrimeExponent p.val.asIdeal r.val : ℂ) * z) := by
  have fc := WeightedFiniteCoefficient.Proof.support_factor A c.val P
    (fun p hp => (hsupport p hp).1)
  have fn := WeightedFiniteCoefficient.Proof.support_factor A n P
    (fun p hp => (hsupport p hp).2.1)
  have fs := WeightedFiniteCoefficient.Proof.support_factor A s P
    (fun p hp => (hsupport p hp).2.2.1)
  have fr := WeightedFiniteCoefficient.Proof.support_factor A r P
    (fun p hp => (hsupport p hp).2.2.2)
  rw [WeightedFiniteCoefficient.Proof.power_factor A c.val P fc (-1 / 2 - ξ),
    WeightedFiniteCoefficient.Proof.power_factor A n P fn (-1 - 3 * ξ),
    WeightedFiniteCoefficient.Proof.power_factor A s P fs (-w),
    WeightedFiniteCoefficient.Proof.power_factor A r P fr (-6 * z)]
  simp only [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  simp only [qPower, LocalFiniteSums.Q, comparisonRealPower, LocalFiniteSums.primeIdeal,
    WeightedFiniteCoefficient.primeIdeal]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

theorem weighted_summand_factorization (U : RawFrequency A)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (c : ExteriorSquarefreeIdeal A.cS) (n s r : A.Exterior)
    (P : Finset (ExteriorPrime A))
    (hsupport : ∀ p : ExteriorPrime A, p ∉ P →
      idealPrimeExponent p.val.asIdeal c.val.val = 0 ∧
      idealPrimeExponent p.val.asIdeal n.val = 0 ∧
      idealPrimeExponent p.val.asIdeal s.val = 0 ∧
      idealPrimeExponent p.val.asIdeal r.val = 0 ∧
      idealPrimeExponent p.val.asIdeal U.ideal.val = 0)
    (ξ w z : ℂ) :
    comparisonEulerPoissonSummand F A D U.u ξ w z c n s r =
      ∏ p ∈ P, localCoefficient C U p
        (idealPrimeExponent p.val.asIdeal c.val.val)
        (idealPrimeExponent p.val.asIdeal n.val)
        (idealPrimeExponent p.val.asIdeal s.val)
        (idealPrimeExponent p.val.asIdeal r.val) *
        qPower p
          (-(idealPrimeExponent p.val.asIdeal c.val.val : ℂ) * (1 / 2 + ξ) -
            (idealPrimeExponent p.val.asIdeal n.val : ℂ) * (1 + 3 * ξ) -
            (idealPrimeExponent p.val.asIdeal s.val : ℂ) * w -
            6 * (idealPrimeExponent p.val.asIdeal r.val : ℂ) * z) := by
  have hnorm := norm_weights_factorization c n s r P
    (fun p hp => ⟨(hsupport p hp).1, (hsupport p hp).2.1,
      (hsupport p hp).2.2.1, (hsupport p hp).2.2.2.1⟩) ξ w z
  unfold comparisonEulerPoissonSummand
  rw [finite_coefficient_factorization U D hD c n s r P hsupport]
  simpa only [← Finset.prod_mul_distrib, mul_assoc] using
    congrArg (fun v : ℂ => (∏ p ∈ P, localCoefficient C U p
      (idealPrimeExponent p.val.asIdeal c.val.val)
      (idealPrimeExponent p.val.asIdeal n.val)
      (idealPrimeExponent p.val.asIdeal s.val)
      (idealPrimeExponent p.val.asIdeal r.val)) * v) hnorm

open CRTEulerSeparation.EulerIndex

def digit (U : RawFrequency A) (ξ w z : ℂ)
    (p : LocalFiniteSums.ExteriorPrime A) (d : FinsuppEulerProduct.Digit) : ℂ :=
  if d.1 ≤ 1 then localCoefficient C U p d.1 d.2.1 d.2.2.1 d.2.2.2 *
    LocalFiniteSums.qPower p (-(d.1 : ℂ) * (1 / 2 + ξ) - (d.2.1 : ℂ) * (1 + 3 * ξ) -
      (d.2.2.1 : ℂ) * w - 6 * (d.2.2.2 : ℂ) * z) else 0

theorem digit_zero (U : RawFrequency A) (ξ w z : ℂ)
    (p : LocalFiniteSums.ExteriorPrime A) : digit (C := C) U ξ w z p 0 = 1 := by
  simp [digit, localCoefficient, LocalFiniteSums.Ctk_zero_zero, LocalFiniteSums.qPower]

theorem coefficient_index (U : RawFrequency A)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (ξ w z : ℂ) (i : CRTAbsoluteSeries.ExteriorIndex A) :
    FinsuppEulerProduct.coefficient (digit (C := C) U ξ w z) (indexEquiv A i).val =
      comparisonEulerPoissonSummand F A D U.u ξ w z i.1 i.2.1 i.2.2.1 i.2.2.2 := by
  let d := (indexEquiv A i).val
  let P := d.support ∪ (idealEquiv A U.ideal).support
  have hs : ∀ p : LocalFiniteSums.ExteriorPrime A, p ∉ P →
      idealPrimeExponent p.val.asIdeal i.1.val.val = 0 ∧
      idealPrimeExponent p.val.asIdeal i.2.1.val = 0 ∧
      idealPrimeExponent p.val.asIdeal i.2.2.1.val = 0 ∧
      idealPrimeExponent p.val.asIdeal i.2.2.2.val = 0 ∧
      idealPrimeExponent p.val.asIdeal U.ideal.val = 0 := by
    intro p hp
    have h := Finset.notMem_union.mp hp
    have hd := Finsupp.notMem_support_iff.mp h.1
    rw [show d p = _ from indexEquiv_apply A i p] at hd
    have hz := Finsupp.notMem_support_iff.mp h.2
    rw [idealEquiv_apply] at hz
    change (_, _, _, _) = (0, 0, 0, 0) at hd
    rcases Prod.mk.inj hd with ⟨h1, hrest⟩
    rcases Prod.mk.inj hrest with ⟨h2, hrest⟩
    rcases Prod.mk.inj hrest with ⟨h3, h4⟩
    exact ⟨h1, h2, h3, h4, hz⟩
  rw [weighted_summand_factorization U D hD i.1 i.2.1 i.2.2.1 i.2.2.2 P hs]
  have he : ∀ p, digit (C := C) U ξ w z p (d p) = localCoefficient C U p
      (idealPrimeExponent p.val.asIdeal i.1.val.val)
      (idealPrimeExponent p.val.asIdeal i.2.1.val)
      (idealPrimeExponent p.val.asIdeal i.2.2.1.val)
      (idealPrimeExponent p.val.asIdeal i.2.2.2.val) *
      LocalFiniteSums.qPower p
        (-(idealPrimeExponent p.val.asIdeal i.1.val.val : ℂ) * (1 / 2 + ξ) -
          (idealPrimeExponent p.val.asIdeal i.2.1.val : ℂ) * (1 + 3 * ξ) -
          (idealPrimeExponent p.val.asIdeal i.2.2.1.val : ℂ) * w -
          6 * (idealPrimeExponent p.val.asIdeal i.2.2.2.val : ℂ) * z) := by
    intro p
    unfold digit
    rw [if_pos ((indexEquiv A i).property p)]
    rw [show d p = _ from indexEquiv_apply A i p]
  change (∏ p ∈ d.support, digit (C := C) U ξ w z p (d p)) = _
  rw [Finset.prod_subset (Finset.subset_union_left : d.support ⊆ P) (fun p hp hpd => ?_)]
  · exact Finset.prod_congr rfl (fun p hp => he p)
  · rw [Finsupp.notMem_support_iff.mp hpd, digit_zero]

theorem coefficient_invalid (U : RawFrequency A) (ξ w z : ℂ)
    (d : LocalFiniteSums.ExteriorPrime A →₀ FinsuppEulerProduct.Digit)
    (hd : ¬ ∀ p, (d p).1 ≤ 1) :
    FinsuppEulerProduct.coefficient (digit (C := C) U ξ w z) d = 0 := by
  push Not at hd
  obtain ⟨p, hp⟩ := hd
  have hps : p ∈ d.support := by
    rw [Finsupp.mem_support_iff]
    intro h
    simp [h] at hp
  exact Finset.prod_eq_zero hps (by simp [digit, not_le.mpr hp])

theorem coefficient_summable (U : RawFrequency A)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (ξ w z : ℂ) (hξ : 3 / 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
    Summable (fun d : LocalFiniteSums.ExteriorPrime A →₀ FinsuppEulerProduct.Digit =>
      ‖FinsuppEulerProduct.coefficient (digit (C := C) U ξ w z) d‖) := by
  have hsub : Summable (fun d : {d : LocalFiniteSums.ExteriorPrime A →₀ FinsuppEulerProduct.Digit //
      ∀ p, (d p).1 ≤ 1} => ‖FinsuppEulerProduct.coefficient (digit (C := C) U ξ w z) d.val‖) := by
    apply (indexEquiv A).summable_iff.mp
    simpa only [Function.comp_def, coefficient_index U D hD ξ w z] using
      comparisonSeries_summable A D σ η hS C.correction hD U.u ξ w z hξ hw hz
  exact (Subtype.val_injective.summable_iff (fun d hd => by
    have hn : ¬ ∀ p, (d p).1 ≤ 1 := by
      intro h
      exact hd ⟨⟨d, h⟩, rfl⟩
    rw [coefficient_invalid (C := C) U ξ w z d hn, norm_zero])).mp hsub

theorem coefficient_tsum (U : RawFrequency A)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (ξ w z : ℂ) :
    (∑' d : LocalFiniteSums.ExteriorPrime A →₀ FinsuppEulerProduct.Digit,
      FinsuppEulerProduct.coefficient (digit (C := C) U ξ w z) d) =
      NormalizedProbe.separatedMellinSeries A D U.u ξ w z := by
  rw [NormalizedProbe.separatedMellinSeries_eq_tsum]
  rw [← tsum_subtype_eq_of_support_subset (s := {d : LocalFiniteSums.ExteriorPrime A →₀
      FinsuppEulerProduct.Digit | ∀ p, (d p).1 ≤ 1}) (by
    intro d hd
    by_contra hn
    exact hd (coefficient_invalid (C := C) U ξ w z d hn))]
  calc
    _ = ∑' i : CRTAbsoluteSeries.ExteriorIndex A,
        FinsuppEulerProduct.coefficient (digit (C := C) U ξ w z) (indexEquiv A i).val :=
      ((indexEquiv A).tsum_eq (fun d => FinsuppEulerProduct.coefficient
        (digit (C := C) U ξ w z) d.val)).symm
    _ = _ := tsum_congr (coefficient_index U D hD ξ w z)

theorem local_tsum (U : RawFrequency A) (ξ w z : ℂ)
    (p : LocalFiniteSums.ExteriorPrime A) :
    (∑' d : FinsuppEulerProduct.Digit, digit (C := C) U ξ w z p d) =
      LocalFiniteSums.f C p (U.j p) (U.theta C p) ξ w z := by
  rw [← tsum_subtype_eq_of_support_subset (s := {d : FinsuppEulerProduct.Digit | d.1 ≤ 1})
    (by
      intro d hd
      by_contra hn
      change ¬ d.1 ≤ 1 at hn
      exact hd (by simp [digit, hn]))]
  calc
    _ = ∑' i : Fin 2 × ℕ × ℕ × ℕ, digit (C := C) U ξ w z p (localIndexEquiv i).val :=
      (localIndexEquiv.tsum_eq (fun d => digit (C := C) U ξ w z p d.val)).symm
    _ = LocalFiniteSums.f C p (U.j p) (U.theta C p) ξ w z := by
      apply tsum_congr
      intro i
      unfold digit
      rw [if_pos (localIndexEquiv i).property]
      rfl

theorem hasProd_local_series (C : A.GeneralArithmeticContext σ η hS) (U : RawFrequency A)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (ξ w z : ℂ) (hξ : 3 / 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
    HasProd (fun p : ExteriorPrime A => f C p (U.j p) (U.theta C p) ξ w z)
      (NormalizedProbe.separatedMellinSeries A D U.u ξ w z) := by
  have h := FinsuppEulerProduct.hasProd (digit (C := C) U ξ w z)
    (digit_zero (C := C) U ξ w z) (coefficient_summable U D hD ξ w z hξ hw hz)
  simpa only [local_tsum, coefficient_tsum U D hD ξ w z] using h

end RawCRT

private theorem raw_primitive_variables_zero
    (C : A.GeneralArithmeticContext σ η hS) (U : RawFrequency A)
    (p : ExteriorPrime A) (hp : (U.j p).val ≠ 0) (ξ w : ℂ) :
    CorrectionFactors.W (σ := σ) p U.u w = 0 ∧
      CorrectionFactors.D (σ := σ) (η := η) p U.u ξ = 0 := by
  obtain ⟨r, a, hr, har, ha⟩ := C.allowed_integral U.ideal
  have hrAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (r : F) (by exact_mod_cast hr.1)) := by
    convert ha using 1
    apply Units.ext
    exact har.symm
  let V : CorrectionFactors.Frequency C := ⟨r, U.ideal, hr, hrAllowed, U.sixthFree⟩
  have hassoc : Associated r U.u := Ideal.span_singleton_eq_span_singleton.mp
    (hr.2.trans U.generates.2.symm)
  obtain ⟨eps, heps⟩ := hassoc
  have hv : (V.j p).val ≠ 0 := hp
  obtain ⟨hW, hD⟩ := CorrectionFactors.primitive_variables_zero C V p hv ξ w
  have hmul : chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) =
      chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) r) *
        chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (eps : A.R)) := by
    rw [← heps, map_mul, map_mul]
  change CorrectionFactors.W (σ := σ) p r w = 0 at hW
  change CorrectionFactors.D (σ := σ) (η := η) p r ξ = 0 at hD
  constructor
  · unfold CorrectionFactors.W at *
    rw [hmul]
    calc
      _ = (chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) r) *
        qPower p (-w)) * chi (σ := σ) p
          (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (eps : A.R)) := by ring
      _ = 0 := by rw [hW, zero_mul]
  · unfold CorrectionFactors.D at *
    rw [hmul, star_mul]
    calc
      _ = (η p.val.asIdeal * star (chi (σ := σ) p
        (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) r)) * qPower p (-ξ)) *
        star (chi (σ := σ) p
          (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (eps : A.R))) := by ring
      _ = 0 := by rw [hD, zero_mul]

 def rawPrimeEquiv : ExteriorPrime A ≃ ExteriorIdealEuler.PrimeIndex A.cS where
  toFun p := ⟨primeIdeal p, p.val.prime⟩
  invFun p := ⟨⟨p.val.val, (Ideal.prime_iff_isPrime p.val.property.1).mp p.property,
    p.val.property.1⟩, p.val.property.2⟩
  left_inv p := by rfl
  right_inv p := by rfl

private lemma raw_normPower_eq (p : ExteriorPrime A) (s : ℂ) :
    (Ideal.absNorm p.val.asIdeal : ℂ) ^ s = qPower p s := by
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
  simp only [Q, SArithmeticData.exteriorNorm, idealNorm, primeIdeal]
  ring

private lemma raw_term_plus (U : RawFrequency A) (p : ExteriorPrime A) (s : ℂ) :
    ExteriorIdealEuler.primeTerm (plusExteriorCoefficient σ U) s (rawPrimeEquiv p) =
      CorrectionFactors.W (σ := σ) p U.u s := by
  change plusExteriorCoefficient σ U (primeIdeal p) *
    (Ideal.absNorm p.val.asIdeal : ℂ) ^ (-s) = _
  rw [raw_normPower_eq]
  rfl

private lemma raw_term_minus (U : RawFrequency A) (p : ExteriorPrime A) (s : ℂ) :
    ExteriorIdealEuler.primeTerm (minusExteriorCoefficient σ η U) s (rawPrimeEquiv p) =
      CorrectionFactors.D (σ := σ) (η := η) p U.u s := by
  change minusExteriorCoefficient σ η U (primeIdeal p) *
    (Ideal.absNorm p.val.asIdeal : ℂ) ^ (-s) = _
  rw [raw_normPower_eq]
  rfl

private lemma raw_term_zeta (p : ExteriorPrime A) (z : ℂ) :
    ExteriorIdealEuler.primeTerm (fun _ : A.Exterior => (1 : ℂ)) (6 * z)
      (rawPrimeEquiv p) = CorrectionFactors.V p z := by
  change 1 * (Ideal.absNorm p.val.asIdeal : ℂ) ^ (-(6 * z)) = _
  rw [one_mul, raw_normPower_eq]
  unfold CorrectionFactors.V
  congr 1
  ring

theorem initial_absolute_euler
    (C : A.GeneralArithmeticContext σ η hS)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (U : RawFrequency A) (ξ w z : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) (hz : z.re = 2) :
    Summable (fun i : ExteriorSquarefreeIdeal A.cS × A.Exterior × A.Exterior × A.Exterior =>
      ‖comparisonEulerPoissonSummand F A D U.u ξ w z
        i.1 i.2.1 i.2.2.1 i.2.2.2‖) ∧
    Multipliable (fun p : ExteriorPrime A => localCorrection C U p ξ w z) ∧
    minusL σ η U ξ ≠ 0 ∧
    comparisonEulerPoissonSeries F A D U.u ξ w z * minusL σ η U ξ =
      InitialSeparatedEuler.zetaS A (6 * z) * plusL σ U w *
        correctionProduct C U ξ w z := by
  have hξ' : 3 / 2 < ξ.re := by rw [hξ]; norm_num
  have hw' : 2 < w.re := by rw [hw]; norm_num
  have hz' : 1 / 6 < z.re := by rw [hz]; norm_num
  have hx : (ξ, w, z) ∈ CorrectionFactors.Omega := by
    apply Or.inl
    change _ ∧ _ ∧ _
    rw [hξ, hw, hz]
    norm_num
  refine ⟨comparisonSeries_summable A D σ η hS C.correction hD U.u ξ w z
    hξ' hw' hz', raw_correction_multipliable C U (ξ, w, z) hx,
    raw_minusL_ne_zero U ξ (by rw [hξ]; norm_num), ?_⟩
  have hξ1 : 1 < ξ.re := by rw [hξ]; norm_num
  have hw1 : 1 < w.re := by rw [hw]; norm_num
  have hz1 : 1 < (6 * z).re := by norm_num [hz]
  have hm := ExteriorIdealEuler.exterior_ideal_euler _ (raw_minus_isCoefficient (σ := σ) (η := η) U) ξ hξ1
  have hp := ExteriorIdealEuler.exterior_ideal_euler _ (raw_plus_isCoefficient (σ := σ) U) w hw1
  have hzeta := ExteriorIdealEuler.exterior_ideal_euler _
    (ExteriorIdealEuler.constant_one_isCoefficient A.cS) (6 * z) hz1
  have hne : minusL σ η U ξ ≠ 0 := raw_minusL_ne_zero U ξ hξ1
  have hDen : HasProd (fun p : ExteriorPrime A =>
      1 - CorrectionFactors.D (σ := σ) (η := η) p U.u ξ) (minusL σ η U ξ)⁻¹ := by
    have h := (rawPrimeEquiv (A := A)).hasProd_iff.mpr hm.2.2.2
    simpa only [Function.comp_def, raw_term_minus, minusL,
      InitialSeparatedEuler.dirichletSeries] using h
  have hW : HasProd (fun p : ExteriorPrime A =>
      (1 - CorrectionFactors.W (σ := σ) p U.u w)⁻¹) (plusL σ U w) := by
    have h := (rawPrimeEquiv (A := A)).hasProd_iff.mpr hp.2.1
    simpa only [Function.comp_def, ExteriorIdealEuler.factor, raw_term_plus,
      plusL, InitialSeparatedEuler.dirichletSeries] using h
  have hV : HasProd (fun p : ExteriorPrime A =>
      (1 - CorrectionFactors.V p z)⁻¹) (InitialSeparatedEuler.zetaS A (6 * z)) := by
    have h := (rawPrimeEquiv (A := A)).hasProd_iff.mpr hzeta.2.1
    simpa only [Function.comp_def, ExteriorIdealEuler.factor, raw_term_zeta,
      ExteriorIdealEuler.summand, one_mul, InitialSeparatedEuler.zetaS] using h
  have hH := (raw_correction_multipliable C U (ξ, w, z) hx).hasProd
  have hprod := ((hDen.mul hV).mul hW).mul hH
  have hlocal (p : ExteriorPrime A) :
      f C p (U.j p) (U.theta C p) ξ w z =
      (1 - CorrectionFactors.D (σ := σ) (η := η) p U.u ξ) *
        (1 - CorrectionFactors.V p z)⁻¹ *
        (1 - CorrectionFactors.W (σ := σ) p U.u w)⁻¹ *
        localCorrection C U p ξ w z := by
    have hsub {a : ℂ} (ha : ‖a‖ < 1) : 1 - a ≠ 0 := by
      intro he
      have he' : a = 1 := (sub_eq_zero.mp he).symm
      simpa [he'] using ha
    have hv : 1 - CorrectionFactors.V p z ≠ 0 := by
      apply hsub
      rw [← raw_term_zeta]
      exact ExteriorIdealEuler.norm_primeTerm_lt_one _
        (ExteriorIdealEuler.constant_one_isCoefficient A.cS) (6 * z) hz1 _
    have hwne : 1 - CorrectionFactors.W (σ := σ) p U.u w ≠ 0 := by
      apply hsub
      rw [← raw_term_plus U]
      exact ExteriorIdealEuler.norm_primeTerm_lt_one _ (raw_plus_isCoefficient U) w hw1 _
    have hdne : 1 - CorrectionFactors.D (σ := σ) (η := η) p U.u ξ ≠ 0 := by
      apply hsub
      rw [← raw_term_minus U]
      exact ExteriorIdealEuler.norm_primeTerm_lt_one _ (raw_minus_isCoefficient U) ξ hξ1 _
    by_cases hj : (U.j p).val = 0
    · have hu : U.u = U.unitPart C p := by
        simpa [hj] using (U.unitPart_spec C p).1
      have hunit := raw_good_unit C U p hj
      have hθ : (U.theta C p).val = chi (σ := σ) p
          (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) := by
        rw [hu]
        rfl
      have hf : f C p (U.j p) (U.theta C p) ξ w z =
          CorrectionFactors.goodRational C p U.u ξ w z := by
        have hformula := (good_euler_series_initial_boundary C p U.u hunit
          (U.theta C p) hθ ξ w z (by rw [hξ]) (by rw [hw]) (by rw [hz])).2
        have hj0 : U.j p = 0 := Fin.ext hj
        rw [hj0]
        simpa [CorrectionFactors.goodRational, CorrectionFactors.V,
          CorrectionFactors.W, CorrectionFactors.D, CorrectionFactors.E, hθ] using hformula
      rw [hf]
      simp only [localCorrection, hj, ↓reduceIte, CorrectionFactors.goodFactor]
      field_simp
    · obtain ⟨hW, hD⟩ := raw_primitive_variables_zero C U p hj ξ w
      simp only [localCorrection, hj, ↓reduceIte, CorrectionFactors.badFactor, hW, hD]
      field_simp
  have hseries : HasProd (fun p : ExteriorPrime A =>
      f C p (U.j p) (U.theta C p) ξ w z)
      (comparisonEulerPoissonSeries F A D U.u ξ w z) :=
    RawCRT.hasProd_local_series C U D hD ξ w z hξ' hw' hz'
  have heq := hseries.unique (hprod.congr_fun hlocal)
  rw [heq]
  change (minusL σ η U ξ)⁻¹ * InitialSeparatedEuler.zetaS A (6 * z) *
    plusL σ U w * correctionProduct C U ξ w z * minusL σ η U ξ = _
  field_simp

theorem initial_euler_quotient
    (C : A.GeneralArithmeticContext σ η hS)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (U : RawFrequency A) (ξ w z : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) (hz : z.re = 2) :
    comparisonEulerPoissonSeries F A D U.u ξ w z =
      InitialSeparatedEuler.zetaS A (6 * z) * plusL σ U w *
        correctionProduct C U ξ w z / minusL σ η U ξ := by
  obtain ⟨_, _, hn, he⟩ := initial_absolute_euler C D hD U ξ w z hξ hw hz
  exact (eq_div_iff hn).mpr he

end DedekindZetaZeroFree.AllRowEuler.InitialSeparation

end
