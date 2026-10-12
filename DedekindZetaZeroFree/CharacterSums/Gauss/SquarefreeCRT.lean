module

public import DedekindZetaZeroFree.Theta.Whittaker.SphericalGeneratorExpansion

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.NumericalSpherical
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain UniqueFactorizationMonoid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem prime_gauss (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) :
    ThetaBranch.gaussTwo R.A R.σ (MomentSources.Characters.psi R) p =
      let r := Classical.choose (R.probe.allowed.generates (ThetaBranch.primeIdeal R.A p))
      R.A.idealGauss R.σ R.traceBad (ThetaBranch.primeIdeal R.A p) r
        (Classical.choose_spec (R.probe.allowed.generates (ThetaBranch.primeIdeal R.A p))).1 2 := by
  let r := Classical.choose (R.probe.allowed.generates (ThetaBranch.primeIdeal R.A p))
  have hr := (Classical.choose_spec (R.probe.allowed.generates (ThetaBranch.primeIdeal R.A p))).1
  have hgen := (Classical.choose_spec (R.probe.allowed.generates (ThetaBranch.primeIdeal R.A p))).2
  change ThetaBranch.gaussTwo R.A R.σ (MomentSources.Characters.psi R) p =
    R.A.idealGauss R.σ R.traceBad (ThetaBranch.primeIdeal R.A p) r hr 2
  let I := ThetaBranch.primeIdeal R.A p
  let E := ArithGaussCRT.exteriorQuotientEquiv R.A I
  letI : Finite (R.A.R ⧸ R.A.extendIdeal I) := R.A.exteriorResidue_finite I
  letI : Fintype (R.A.R ⧸ R.A.extendIdeal I) := Fintype.ofFinite _
  have hadd (d : DHCubic.Residue F p.val) :
      MomentSources.Characters.psi R p d = (R.A.residueTraceCharacter R.traceBad I r hr (E d) : ℂ) := by
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [MomentSources.Characters.psi_apply]
    change _ = ((R.A.residueTraceCharacter R.traceBad I r hr)
      (E (Ideal.Quotient.mk I.val t)) : ℂ)
    rw [ArithGaussCRT.exteriorQuotientEquiv_mk,
      R.A.residueTraceCharacter_apply, PrincipalMellinSource.additiveCharacter_eq_fieldTrace,
      hgen]
    rfl
  have hmul (d : DHCubic.Residue F p.val) :
      (ThetaBranch.residueCharacter R.A R.σ p ^ 2) d =
        R.A.sexticResiduePowerChar R.σ I 2 (E d) := by
    rw [MulChar.pow_apply' _ (by norm_num : (2 : ℕ) ≠ 0),
      NormalizedProbe.principal_prime_residueCharacter_transport]
    simp only [SArithmeticData.sexticResiduePowerChar,
      show SArithmeticData.sexticExponent (1 : ℤ) = 1 from rfl,
      show SArithmeticData.sexticExponent (2 : ℤ) = 2 from rfl, pow_one,
      MulChar.pow_apply' _ (by norm_num : (2 : ℕ) ≠ 0)]
    rfl
  have hcard : (Fintype.card (DHCubic.Residue F p.val) : ℝ) = R.A.exteriorNorm I := by
    simp only [SArithmeticData.exteriorNorm, idealNorm, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Nat.card_eq_fintype_card, I, ThetaBranch.primeIdeal]
  unfold ThetaBranch.gaussTwo SArithmeticData.idealGauss
  rw [hcard]
  congr 1
  unfold gaussSum
  change (∑ d : DHCubic.Residue F p.val, _) = ∑ x : R.A.R ⧸ R.A.extendIdeal I, _
  let E' : DHCubic.Residue F p.val ≃ R.A.R ⧸ R.A.extendIdeal I := E.toEquiv
  refine Fintype.sum_equiv E' _ _ ?_
  intro d
  rw [hmul, hadd]
  rfl

theorem squarefree_exps (A : SArithmeticData F) (d : ExteriorSquarefreeIdeal A.cS)
    (p : ThetaBranch.ExteriorPrime A) :
    idealPrimeExponent p.val.asIdeal d.val.val = 0 ∨ idealPrimeExponent p.val.asIdeal d.val.val = 1 := by
  have hh := Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors d.val.property.1).mp d.property) p.val.asIdeal
  change idealPrimeExponent p.val.asIdeal d.val.val ≤ 1 at hh
  omega

theorem gauss_finiteProduct (R : PrincipalMellin.ActualRecipe S η)
    (d : ExteriorSquarefreeIdeal R.A.cS) (P : Finset (ThetaBranch.ExteriorPrime R.A))
    (hd : d.val.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal d.val.val) :
    let e := fun p : ThetaBranch.ExteriorPrime R.A => idealPrimeExponent p.val.asIdeal d.val.val
    let r := fun p : ThetaBranch.ExteriorPrime R.A =>
      Classical.choose (R.probe.allowed.generates (ThetaBranch.primeIdeal R.A p))
    R.probe.coefficients.gammaTwo d =
      (∏ p ∈ P, ThetaBranch.gaussTwo R.A R.σ (MomentSources.Characters.psi R) p ^ e p) *
      (∏ p ∈ P, ∏ q ∈ P.erase p,
        R.σ (R.A.sexticResidue (ThetaBranch.primeIdeal R.A p) (r q)) ^ (2 * e p * e q)) := by
  classical
  letI : DecidableEq (ThetaBranch.ExteriorPrime R.A) := Classical.decEq _
  dsimp only
  let A := R.A
  let G := R.probe.allowed
  let e := fun p : ThetaBranch.ExteriorPrime A => idealPrimeExponent p.val.asIdeal d.val.val
  let r := fun p : ThetaBranch.ExteriorPrime A => Classical.choose (G.generates (ThetaBranch.primeIdeal A p))
  have hr (p : ThetaBranch.ExteriorPrime A) : A.Generates (ThetaBranch.primeIdeal A p) (r p) :=
    (Classical.choose_spec (G.generates (ThetaBranch.primeIdeal A p))).1
  have hu (p : ThetaBranch.ExteriorPrime A) : (G.generator (ThetaBranch.primeIdeal A p) : F) = (r p : F) :=
    (Classical.choose_spec (G.generates (ThetaBranch.primeIdeal A p))).2
  have he (p : ThetaBranch.ExteriorPrime A) : e p = 0 ∨ e p = 1 := squarefree_exps A d p
  let Q : ThetaBranch.ExteriorPrime A → A.Exterior := fun p =>
    if e p = 0 then (exteriorSquarefreeTop A.cS).val else ThetaBranch.primeIdeal A p
  let ρ : ThetaBranch.ExteriorPrime A → A.R := fun p => r p ^ e p
  let a : ThetaBranch.ExteriorPrime A → Fˣ := fun p => G.generator (ThetaBranch.primeIdeal A p) ^ e p
  have hρ (p : ThetaBranch.ExteriorPrime A) : A.Generates (Q p) (ρ p) := by
    rcases he p with hz | ho
    · simp [Q, ρ, hz, SArithmeticData.Generates, SArithmeticData.extendIdeal, exteriorSquarefreeTop,
        Ideal.map_top]
    · simpa [Q, ρ, ho] using hr p
  have hQ : d.val.val = ∏ p ∈ P, (Q p).val := by
    rw [hd]
    apply Finset.prod_congr rfl
    intro p hp
    rcases he p with hz | ho
    · simp [Q, hz, ← show e p = idealPrimeExponent p.val.asIdeal d.val.val from rfl, exteriorSquarefreeTop]
    · simp [Q, ho, ← show e p = idealPrimeExponent p.val.asIdeal d.val.val from rfl, ThetaBranch.primeIdeal]
  have hcop : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (Q p).val ⊔ (Q q).val = ⊤ := by
    intro p hp q hq hpq
    rcases he p with hz | ho
    · simp [Q, hz, exteriorSquarefreeTop]
    rcases he q with hz | ho'
    · simp [Q, hz, exteriorSquarefreeTop]
    simp only [Q, ho, ho', one_ne_zero, ↓reduceIte, ThetaBranch.primeIdeal]
    exact (p.val.isCoprime_of_ne q.val (fun hh => hpq (Subtype.ext hh))).sup_eq
  have hgen : A.Generates d.val (∏ p ∈ P, ρ p) := by
    refine ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => (hρ p).1), ?_⟩
    rw [← Ideal.prod_span_singleton]
    simp_rw [(hρ _).2]
    simp only [SArithmeticData.extendIdeal, hQ]
    exact (map_prod (Ideal.mapHom (algebraMap (𝓞 F) A.R)) _ _).symm
  have hval : ((∏ p ∈ P, a p : Fˣ) : F) = ((∏ p ∈ P, ρ p : A.R) : F) := by
    rw [Units.coe_prod]
    change _ = A.R.subtype (∏ p ∈ P, ρ p)
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro p hp
    simp only [a, ρ, Units.val_pow_eq_pow_val, map_pow, hu p]
    rfl
  have hall (p : ThetaBranch.ExteriorPrime A) : A.IsAllowed R.probe.correction.B (a p) := by
    change A.sClass (G.generator (ThetaBranch.primeIdeal A p) ^ e p) ∈ _
    rw [map_pow]
    have hh : A.sClass (G.generator (ThetaBranch.primeIdeal A p)) ∈ R.probe.correction.B := by
      rw [← R.probe.sameComplement]
      exact G.allowed _
    exact R.probe.correction.B.pow_mem hh _
  have hallowed : A.IsAllowed R.probe.correction.B (∏ p ∈ P, a p) := by
    clear hd hQ hcop hgen hval
    induction P using Finset.induction_on with
    | empty => exact R.probe.correction.B.one_mem
    | @insert p P hp ih =>
      rw [Finset.prod_insert hp]
      change A.sClass (a p * ∏ q ∈ P, a q) ∈ _
      rw [map_mul]
      exact R.probe.correction.B.mul_mem (hall p) ih
  have hb : A.IsAllowed R.probe.correction.B (G.generator d.val) := by
    change A.sClass (G.generator d.val) ∈ _
    rw [← R.probe.sameComplement]
    exact G.allowed _
  have hind := A.idealGauss_allowed_generator_independent R.σ R.traceBad R.classKilled
    R.probe.correction.H R.probe.correction.B R.probe.correction.B_complement d.val
    (∏ p ∈ P, ρ p) (R.probe.coefficients.generator d.val)
    hgen (R.probe.coefficients.generates d.val) (∏ p ∈ P, a p) (G.generator d.val)
    hval (R.probe.sameGenerator d.val) hallowed hb 2
  rw [R.probe.gammaTwo_eq_idealGauss, hind,
    GlobalPairCancel.idealGauss_finite_support_crt A R.σ R.traceBad Q ρ hρ P
      (hQ ▸ d.property) hcop d.val hQ hgen]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    rcases he p with hz | ho
    · have ht : (Q p).val = ⊤ := by simp [Q, hz, exteriorSquarefreeTop]
      rw [A.idealGauss_top R.σ R.traceBad (Q p) ht (ρ p) (hρ p) 2]
      simp [← show e p = idealPrimeExponent p.val.asIdeal d.val.val from rfl, hz]
    · simp only [← show e p = idealPrimeExponent p.val.asIdeal d.val.val from rfl, ho, pow_one]
      simpa only [Q, ρ, ho, one_ne_zero, ↓reduceIte, pow_one] using (prime_gauss R p).symm
  · dsimp only [A, G] at *
    unfold GlobalPairCancel.frequencyTheta
    apply Finset.prod_congr rfl
    intro p hp
    have hphase : R.σ (R.A.sexticResidue (Q p) (∏ w ∈ P.erase p, ρ w)) ^ 2 =
        ∏ q ∈ P.erase p, R.σ (R.A.sexticResidue (ThetaBranch.primeIdeal R.A p) (r q)) ^ (2 * e p * e q) := by
      rcases he p with hz | ho
      · change R.σ (R.A.sexticResidue (Q p) _) ^ 2 = _
        have ht : (Q p).val = ⊤ := by simp [Q, hz, exteriorSquarefreeTop]
        rw [show R.A.sexticResidue (Q p) (∏ w ∈ P.erase p, ρ w) = 1 from
          R.A.residueValue_top R.A.sexticResidueFamily (Q p) ht _]
        simp [← show e p = idealPrimeExponent p.val.asIdeal d.val.val from rfl, hz]
      · change R.σ (R.A.sexticResidue (Q p) _) ^ 2 = _
        simp only [Q, ho, one_ne_zero, ↓reduceIte]
        unfold SArithmeticData.sexticResidue SArithmeticData.residueValue
        simp only [map_prod, ← Finset.prod_pow, map_pow, ρ]
        apply Finset.prod_congr rfl
        intro q hq
        change (R.σ (R.A.sexticResidue (ThetaBranch.primeIdeal R.A p) (r q)) ^ e q) ^ 2 = _
        rw [← pow_mul]
        congr 1
        ring
    convert hphase using 1
    congr 1
    ext q; simp

end DedekindZetaZeroFree.ExteriorWhittakerValues.NumericalSpherical

end
