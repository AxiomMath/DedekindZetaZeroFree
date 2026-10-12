module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.AbsoluteDigitSeries
public import DedekindZetaZeroFree.Moments.Principal.Corrections.Definitions

@[expose] public section

open scoped NumberField Classical
open IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.CRTEulerSeparation
set_option autoImplicit false

open LocalFiniteSums CorrectionFactors

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}

def localCoefficient (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C)
    (p : ExteriorPrime A) (e l k m : ℕ) : ℂ :=
  gammaTwo C p ^ e * vartheta C p ^ (e + 3 * l) *
    (U.theta p).val ^ ((k : ℤ) - (e : ℤ) - 3 * (l : ℤ)) *
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

private theorem phase_eq (U : Frequency C) (p : ExteriorPrime A) :
    (U.theta p).val = GlobalPairCancel.frequencyTheta A σ (primeIdeal p) (U.unitPart p) := by
  change A.sexticResiduePowerChar σ (primeIdeal p) 1
    (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (U.unitPart p)) = _
  unfold SArithmeticData.sexticResiduePowerChar
  rw [show SArithmeticData.sexticExponent 1 = 1 by decide, pow_one]
  unfold GlobalPairCancel.frequencyTheta SArithmeticData.sexticResidue SArithmeticData.residueValue
  have hx := (U.unitPart_spec p).2
  rw [← hx.unit_spec, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
  rfl

theorem finite_coefficient_factorization (U : Frequency C)
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
  have hraw := (GlobalPairCancel.global_pair_cancel A C.classGroup_trivial σ η hS C.correction D hrec
    c n s r U.ideal U.u U.generates (WeightedFiniteCoefficient.fieldUnit A U.u U.generates.1)
    rfl U.allowed hsix Q
    (fun v => primeIdeal (ep v)) (fun v => congrArg HeightOneSpectrum.asIdeal (hep v))
    (fun v => generator C (ep v)) (fun v => generator_generates C (ep v))
    (fun v => WeightedFiniteCoefficient.fieldUnit A _ (generator_generates C (ep v)).1)
    (fun v => rfl) (fun v => generator_allowed C (ep v)) hfac
    (fun v => U.unitPart (ep v))
    (fun v => by simpa only [← hep v, Frequency.j] using (U.unitPart_spec (ep v)).1)
    (fun v => (U.unitPart_spec (ep v)).2)).2
  have hrawP : D.gammaTwo c * comparisonPoissonFiniteCoefficient F A D c n s
      (U.u * D.generator r ^ 6) = ∏ p ∈ P,
      gammaTwo C p ^ idealPrimeExponent p.val.asIdeal c.val.val *
      (U.theta p).val ^ ((idealPrimeExponent p.val.asIdeal s.val : ℤ) -
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
  dsimp only [Frequency.j]
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

theorem weighted_summand_factorization (U : Frequency C)
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

theorem series_summable (U : Frequency C)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    Summable (fun i : CRTAbsoluteSeries.ExteriorIndex A =>
      ‖comparisonEulerPoissonSummand F A D U.u ξ w z
        i.1 i.2.1 i.2.2.1 i.2.2.2‖) := by
  exact CRTAbsoluteSeries.weightedSummand_summable A D C.classGroup_trivial σ η hS
    C.correction hD U.ideal U.u U.generates U.allowed
    (fun p => by have h := U.sixthFree p; omega) ξ w z hξ hw hz

namespace EulerIndex
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
def primeEquiv : LocalFiniteSums.ExteriorPrime A ≃ ExteriorEulerPrimeIndex.exteriorPrimeRawIndex A.cS where
  toFun p := ⟨⟨p.val.asIdeal, p.val.ne_bot, p.property⟩, p.val.prime⟩
  invFun p := ⟨⟨p.val.val, Ideal.isPrime_of_prime p.property, p.property.ne_zero⟩, p.val.property.2⟩
  left_inv p := rfl
  right_inv p := rfl

def idealEquiv : A.Exterior ≃ (LocalFiniteSums.ExteriorPrime A →₀ ℕ) :=
  (ExteriorEulerPrimeIndex.exponentEquiv A.cS).trans (Finsupp.domCongr (primeEquiv A).symm).toEquiv
theorem idealEquiv_apply (I : A.Exterior) (p : LocalFiniteSums.ExteriorPrime A) :
    idealEquiv A I p = idealPrimeExponent p.val.asIdeal I.val := by
  rfl

theorem squarefree_iff (I : A.Exterior) :
    Squarefree I.val ↔ ∀ p : LocalFiniteSums.ExteriorPrime A, idealEquiv A I p ≤ 1 := by
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors I.property.1,
    Multiset.nodup_iff_count_le_one]
  constructor
  · intro h p
    exact h p.val.asIdeal
  · intro h q
    by_cases hq : q ∈ UniqueFactorizationMonoid.normalizedFactors I.val
    · have hp := UniqueFactorizationMonoid.prime_of_normalized_factor q hq
      have hc : q ⊔ A.cS = ⊤ := by
        apply top_unique
        rw [← I.property.2]
        exact sup_le_sup_right (Ideal.dvd_iff_le.mp
          (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq)) _
      exact h ⟨⟨q, Ideal.isPrime_of_prime hp, hp.ne_zero⟩, hc⟩
    · simp [Multiset.count_eq_zero_of_notMem hq]

variable {P : Type} [DecidableEq P]
def zipEquiv : (P →₀ ℕ) × (P →₀ ℕ) × (P →₀ ℕ) × (P →₀ ℕ) ≃
    (P →₀ FinsuppEulerProduct.Digit) where
  toFun v := Finsupp.onFinset (v.1.support ∪ v.2.1.support ∪ v.2.2.1.support ∪ v.2.2.2.support)
    (fun p => (v.1 p, v.2.1 p, v.2.2.1 p, v.2.2.2 p)) (by
      intro p hp
      contrapose! hp
      simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or] at hp
      simp only [not_not] at hp
      simp [hp.1.1.1, hp.1.1.2, hp.1.2, hp.2])
  invFun d := (d.mapRange Prod.fst rfl, d.mapRange (fun δ => δ.2.1) rfl,
    d.mapRange (fun δ => δ.2.2.1) rfl, d.mapRange (fun δ => δ.2.2.2) rfl)
  left_inv v := by
    rcases v with ⟨c,n,s,r⟩
    simp only [Prod.mk.injEq]
    repeat' constructor
    all_goals ext p; rfl
  right_inv d := by ext p <;> rfl

def allIndexEquiv : (A.Exterior × A.Exterior × A.Exterior × A.Exterior) ≃
    (LocalFiniteSums.ExteriorPrime A →₀ FinsuppEulerProduct.Digit) :=
  (Equiv.prodCongr (idealEquiv A)
    (Equiv.prodCongr (idealEquiv A) (Equiv.prodCongr (idealEquiv A) (idealEquiv A)))).trans zipEquiv

def indexEquiv : CRTAbsoluteSeries.ExteriorIndex A ≃
    {d : LocalFiniteSums.ExteriorPrime A →₀ FinsuppEulerProduct.Digit // ∀ p, (d p).1 ≤ 1} :=
  Equiv.prodSubtypeFstEquivSubtypeProd.symm.trans
    ((allIndexEquiv A).subtypeEquiv (fun i => squarefree_iff A i.1))

theorem indexEquiv_apply (i : CRTAbsoluteSeries.ExteriorIndex A)
    (p : LocalFiniteSums.ExteriorPrime A) :
    (indexEquiv A i).val p = (idealPrimeExponent p.val.asIdeal i.1.val.val,
      idealPrimeExponent p.val.asIdeal i.2.1.val,
      idealPrimeExponent p.val.asIdeal i.2.2.1.val,
      idealPrimeExponent p.val.asIdeal i.2.2.2.val) := by rfl

variable {A} {σ : F →+* ℂ} {η : RayClassCharacter F A.modulus}
  {hS : A.ContainsTraceBadPlaces} {C : A.GeneralArithmeticContext σ η hS}

def digit (U : CorrectionFactors.Frequency C) (ξ w z : ℂ)
    (p : LocalFiniteSums.ExteriorPrime A) (d : FinsuppEulerProduct.Digit) : ℂ :=
  if d.1 ≤ 1 then localCoefficient C U p d.1 d.2.1 d.2.2.1 d.2.2.2 *
    LocalFiniteSums.qPower p (-(d.1 : ℂ) * (1 / 2 + ξ) - (d.2.1 : ℂ) * (1 + 3 * ξ) -
      (d.2.2.1 : ℂ) * w - 6 * (d.2.2.2 : ℂ) * z) else 0

theorem digit_zero (U : CorrectionFactors.Frequency C) (ξ w z : ℂ)
    (p : LocalFiniteSums.ExteriorPrime A) : digit U ξ w z p 0 = 1 := by
  simp [digit, localCoefficient, LocalFiniteSums.Ctk_zero_zero, LocalFiniteSums.qPower]

theorem coefficient_index (U : CorrectionFactors.Frequency C)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (ξ w z : ℂ) (i : CRTAbsoluteSeries.ExteriorIndex A) :
    FinsuppEulerProduct.coefficient (digit U ξ w z) (indexEquiv A i).val =
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
  have he : ∀ p, digit U ξ w z p (d p) = localCoefficient C U p
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
  change (∏ p ∈ d.support, digit U ξ w z p (d p)) = _
  rw [Finset.prod_subset (Finset.subset_union_left : d.support ⊆ P) (fun p hp hpd => ?_)]
  · exact Finset.prod_congr rfl (fun p hp => he p)
  · rw [Finsupp.notMem_support_iff.mp hpd, digit_zero]

theorem coefficient_invalid (U : CorrectionFactors.Frequency C) (ξ w z : ℂ)
    (d : LocalFiniteSums.ExteriorPrime A →₀ FinsuppEulerProduct.Digit)
    (hd : ¬ ∀ p, (d p).1 ≤ 1) :
    FinsuppEulerProduct.coefficient (digit U ξ w z) d = 0 := by
  push Not at hd
  obtain ⟨p, hp⟩ := hd
  have hps : p ∈ d.support := by
    rw [Finsupp.mem_support_iff]
    intro h
    simp [h] at hp
  exact Finset.prod_eq_zero hps (by simp [digit, not_le.mpr hp])

theorem coefficient_summable (U : CorrectionFactors.Frequency C)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    Summable (fun d : LocalFiniteSums.ExteriorPrime A →₀ FinsuppEulerProduct.Digit =>
      ‖FinsuppEulerProduct.coefficient (digit U ξ w z) d‖) := by
  have hsub : Summable (fun d : {d : LocalFiniteSums.ExteriorPrime A →₀ FinsuppEulerProduct.Digit //
      ∀ p, (d p).1 ≤ 1} => ‖FinsuppEulerProduct.coefficient (digit U ξ w z) d.val‖) := by
    apply (indexEquiv A).summable_iff.mp
    simpa only [Function.comp_def, coefficient_index U D hD ξ w z] using
      series_summable U D hD ξ w z hξ hw hz
  exact (Subtype.val_injective.summable_iff (fun d hd => by
    have hn : ¬ ∀ p, (d p).1 ≤ 1 := by
      intro h
      exact hd ⟨⟨d, h⟩, rfl⟩
    rw [coefficient_invalid U ξ w z d hn, norm_zero])).mp hsub

theorem coefficient_tsum (U : CorrectionFactors.Frequency C)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (ξ w z : ℂ) :
    (∑' d : LocalFiniteSums.ExteriorPrime A →₀ FinsuppEulerProduct.Digit,
      FinsuppEulerProduct.coefficient (digit U ξ w z) d) =
      NormalizedProbe.separatedMellinSeries A D U.u ξ w z := by
  rw [NormalizedProbe.separatedMellinSeries_eq_tsum]
  rw [← tsum_subtype_eq_of_support_subset (s := {d : LocalFiniteSums.ExteriorPrime A →₀
      FinsuppEulerProduct.Digit | ∀ p, (d p).1 ≤ 1}) (by
    intro d hd
    by_contra hn
    exact hd (coefficient_invalid U ξ w z d hn))]
  calc
    _ = ∑' i : CRTAbsoluteSeries.ExteriorIndex A,
        FinsuppEulerProduct.coefficient (digit U ξ w z) (indexEquiv A i).val :=
      ((indexEquiv A).tsum_eq (fun d => FinsuppEulerProduct.coefficient
        (digit U ξ w z) d.val)).symm
    _ = _ := tsum_congr (coefficient_index U D hD ξ w z)

def localIndexEquiv : (Fin 2 × ℕ × ℕ × ℕ) ≃
    {d : FinsuppEulerProduct.Digit // d.1 ≤ 1} where
  toFun i := ⟨(i.1.val, i.2), by have h := i.1.isLt; omega⟩
  invFun d := (⟨d.val.1, by have h := d.property; omega⟩, d.val.2)
  left_inv i := rfl
  right_inv d := rfl

theorem local_tsum (U : CorrectionFactors.Frequency C) (ξ w z : ℂ)
    (p : LocalFiniteSums.ExteriorPrime A) :
    (∑' d : FinsuppEulerProduct.Digit, digit U ξ w z p d) =
      LocalFiniteSums.f C p (U.j p) (U.theta p) ξ w z := by
  rw [← tsum_subtype_eq_of_support_subset (s := {d : FinsuppEulerProduct.Digit | d.1 ≤ 1})
    (by
      intro d hd
      by_contra hn
      change ¬ d.1 ≤ 1 at hn
      exact hd (by simp [digit, hn]))]
  calc
    _ = ∑' i : Fin 2 × ℕ × ℕ × ℕ, digit U ξ w z p (localIndexEquiv i).val :=
      (localIndexEquiv.tsum_eq (fun d => digit U ξ w z p d.val)).symm
    _ = LocalFiniteSums.f C p (U.j p) (U.theta p) ξ w z := by
      apply tsum_congr
      intro i
      unfold digit
      rw [if_pos (localIndexEquiv i).property]
      rfl

end EulerIndex

theorem hasProd_local_series (U : Frequency C)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    HasProd (fun p : ExteriorPrime A => f C p (U.j p) (U.theta p) ξ w z)
      (NormalizedProbe.separatedMellinSeries A D U.u ξ w z) := by
  have h := FinsuppEulerProduct.hasProd (EulerIndex.digit U ξ w z)
    (EulerIndex.digit_zero U ξ w z) (EulerIndex.coefficient_summable U D hD ξ w z hξ hw hz)
  simpa only [EulerIndex.local_tsum, EulerIndex.coefficient_tsum U D hD ξ w z] using h

end DedekindZetaZeroFree.CRTEulerSeparation

end
