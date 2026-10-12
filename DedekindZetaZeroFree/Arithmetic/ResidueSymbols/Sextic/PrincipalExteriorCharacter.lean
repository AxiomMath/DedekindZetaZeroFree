module

public import DedekindZetaZeroFree.Moments.Probes.PrincipalProbeAndSeparatedMellinSeries

@[expose] public section

namespace DedekindZetaZeroFree.NormalizedProbe

noncomputable section
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

open NumberField IsDedekindDomain UniqueFactorizationMonoid
set_option backward.isDefEq.respectTransparency false

theorem principal_row_unitResidue_transport (A : SArithmeticData F) (p : ThetaBranch.ExteriorPrime A)
    (t : A.R) (ht : t ≠ 0) :
    ArithGaussCRT.exteriorQuotientEquiv A (ThetaBranch.primeIdeal A p)
      (ThetaBranch.unitResidue p.val (ThetaReflectionData.rowUnit A ⟨t, ht⟩)) =
        Ideal.Quotient.mk (A.extendIdeal (ThetaBranch.primeIdeal A p)) t := by
  let I := ThetaBranch.primeIdeal A p
  let E := ArithGaussCRT.exteriorQuotientEquiv A I
  obtain ⟨n, d, hd⟩ := p.val.exists_primeCompl_mul_eq_of_integer (t : F)
    (t.property p.val p.property)
  have hdv : p.val.valuation F (d : 𝓞 F) = 1 :=
    p.val.valuation_eq_one_iff_notMem.mpr d.property
  change (t : F) * (d : 𝓞 F) = (n : F) at hd
  have hnval : p.val.valuation F (n : F) = p.val.valuation F (t : F) := by
    rw [← hd, map_mul, hdv, mul_one]
  have hdiv : (t : F) = (n : F) / (d : 𝓞 F) := by
    exact (eq_div_iff (by
      intro hz
      have : (d : 𝓞 F) = 0 := RingOfIntegers.ext hz
      exact d.property (this ▸ p.val.asIdeal.zero_mem))).mpr hd
  have heq : Ideal.Quotient.mk (A.extendIdeal I) t *
      E (Ideal.Quotient.mk I.val (d : 𝓞 F)) = E (Ideal.Quotient.mk I.val n) := by
    rw [ArithGaussCRT.exteriorQuotientEquiv_mk,
      ArithGaussCRT.exteriorQuotientEquiv_mk, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hd
  have hdq : Ideal.Quotient.mk I.val (d : 𝓞 F) ≠ 0 := by
    exact fun h => d.property (Ideal.Quotient.eq_zero_iff_mem.mp h)
  letI : I.val.IsMaximal := p.val.isMaximal
  letI : Field (𝓞 F ⧸ I.val) := Ideal.Quotient.field I.val
  have hred : E (Ideal.Quotient.mk I.val n / Ideal.Quotient.mk I.val (d : 𝓞 F)) =
      Ideal.Quotient.mk (A.extendIdeal I) t := by
    apply E.symm.injective
    rw [E.symm_apply_apply]
    apply (div_eq_iff hdq).mpr
    apply E.injective
    simpa only [map_mul, E.apply_symm_apply] using heq.symm
  by_cases hx : ThetaBranch.order p.val (ThetaReflectionData.rowUnit A ⟨t, ht⟩) = 0
  · have hn : n ∉ p.val.asIdeal := by
      apply p.val.valuation_eq_one_iff_notMem (K := F) |>.mp
      rw [hnval]
      have hh : WithZero.log (p.val.valuation F (t : F)) = 0 := neg_eq_zero.mp hx
      have hne : p.val.valuation F (t : F) ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr (by exact_mod_cast ht)
      rw [← WithZero.exp_log hne, hh, WithZero.exp_zero]
    have hr : ThetaBranch.IsUnitResidue p.val
        (ThetaReflectionData.rowUnit A ⟨t, ht⟩)
        (Ideal.Quotient.mk I.val n / Ideal.Quotient.mk I.val (d : 𝓞 F)) :=
      ⟨n, d, hn, d.property, hdiv, rfl⟩
    have hu : ThetaBranch.unitResidue p.val (ThetaReflectionData.rowUnit A ⟨t, ht⟩) =
        Ideal.Quotient.mk I.val n / Ideal.Quotient.mk I.val (d : 𝓞 F) :=
      (ThetaBranch.existsUnique_unitResidue p.val
      (ThetaReflectionData.rowUnit A ⟨t, ht⟩) hx).unique
      (by simpa only [ThetaBranch.unitResidue, dif_pos hx] using
        (ThetaBranch.existsUnique_unitResidue p.val
          (ThetaReflectionData.rowUnit A ⟨t, ht⟩) hx).exists.choose_spec) hr
    rw [hu]
    exact hred
  · have hn : n ∈ p.val.asIdeal := by
      by_contra hn
      apply hx
      change -WithZero.log (p.val.valuation F (t : F)) = 0
      rw [← hnval, p.val.valuation_eq_one_iff_notMem.mpr hn]
      simp
    rw [ThetaBranch.unitResidue, dif_neg hx, map_zero]
    have hnq : Ideal.Quotient.mk I.val n = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hn
    simpa only [hnq, zero_div, map_zero] using hred

theorem principal_prime_residueCharacter_transport
    (A : SArithmeticData F) (σ : F →+* ℂ) (p : ThetaBranch.ExteriorPrime A)
    (y : DHCubic.Residue F p.val) :
    ThetaBranch.residueCharacter A σ p y =
      A.sexticResiduePowerChar σ (ThetaBranch.primeIdeal A p) 1
        (ArithGaussCRT.exteriorQuotientEquiv A (ThetaBranch.primeIdeal A p) y) := by
  let I := ThetaBranch.primeIdeal A p
  let E := ArithGaussCRT.exteriorQuotientEquiv A I
  let χ := (DHCubic.existsUnique_normalizedSextic F A p.val p.property).exists.choose
  letI : Nontrivial (𝓞 F ⧸ I.val) := Ideal.Quotient.nontrivial_iff.mpr p.val.isPrime.ne_top
  have hχ := (DHCubic.existsUnique_normalizedSextic F A p.val p.property).exists.choose_spec
  have hpow : SArithmeticData.sexticExponent (1 : ℤ) = 1 := by decide
  simp only [SArithmeticData.sexticResiduePowerChar, hpow, pow_one]
  change σ (algebraMap (𝓞 F) F (χ y)) = _
  by_cases hy : y = 0
  · subst y
    have hnu : ¬ IsUnit (E 0) := by
      intro hu
      have hh := hu.map E.symm.toRingHom
      change IsUnit (E.symm (E 0)) at hh
      rw [E.symm_apply_apply] at hh
      exact not_isUnit_zero hh
    rw [MulChar.map_zero, map_zero, map_zero, MulChar.map_nonunit _ hnu]
  · let u := Units.map E.toMonoidHom (Units.mk0 y hy)
    have hu : (u : A.R ⧸ A.extendIdeal I) = E y := rfl
    obtain ⟨j, hj, hej, hred⟩ := A.sexticResidueFamily_normalized.2.1 I p.val rfl u
    obtain ⟨⟨k, hk, hek⟩, hrek⟩ := hχ y hy
    have hcard : Nat.card (A.R ⧸ A.extendIdeal I) = Fintype.card (DHCubic.Residue F p.val) := by
      rw [← Nat.card_eq_fintype_card]
      exact (Nat.card_congr E.toEquiv).symm
    have hredk : Ideal.Quotient.mk (A.extendIdeal I)
        (algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ (2 * k))) =
        (u : A.R ⧸ A.extendIdeal I) ^ ((Nat.card (A.R ⧸ A.extendIdeal I) - 1) / 6) := by
      rw [hu, hcard, ← ArithGaussCRT.exteriorQuotientEquiv_mk A I, ← hek]
      change E (Ideal.Quotient.mk p.val.asIdeal (χ y)) = _
      rw [hrek, map_pow]
    have hp := A.exterior_sextic_primitive I p.val.isPrime.ne_top
    have hjk : j = k := hp.pow_inj hj hk (by
      simpa only [← map_pow, pow_mul, map_pow] using hred.trans hredk.symm)
    rw [← hu, MulChar.ofUnitHom_coe]
    change σ (algebraMap (𝓞 F) F (χ y)) = σ ((A.sexticResidueFamily I u : F))
    rw [hej, hek, hjk, map_pow]
    exact congrArg (fun z : F => σ (z ^ (2 * k))) A.primitive_zeta12.coe_toInteger

theorem principal_prime_symbol_eq_sexticResiduePowerChar
    (A : SArithmeticData F) (σ : F →+* ℂ) (p : ThetaBranch.ExteriorPrime A)
    (t : A.R) (ht : t ≠ 0) :
    ThetaBranch.symbol A σ p (ThetaReflectionData.rowUnit A ⟨t, ht⟩) =
      A.sexticResiduePowerChar σ (ThetaBranch.primeIdeal A p) 1
        (Ideal.Quotient.mk (A.extendIdeal (ThetaBranch.primeIdeal A p)) t) := by
  rw [ThetaBranch.symbol, principal_prime_residueCharacter_transport,
    principal_row_unitResidue_transport]

private theorem char_one (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (t : A.R) :
    A.sexticResiduePowerChar σ I 1 (Ideal.Quotient.mk (A.extendIdeal I) t) =
      σ (A.sexticResidue I t) := by
  have hp : SArithmeticData.sexticExponent (1 : ℤ) = 1 := by decide
  simp only [SArithmeticData.sexticResiduePowerChar, hp, pow_one]
  by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) t)
  · change _ = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [← hx.unit_spec, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
    rfl
  · rw [MulChar.map_nonunit _ hx]
    change 0 = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [MulChar.map_nonunit _ hx, map_zero]

 def primeEval (A : SArithmeticData F) (σ : F →+* ℂ) (t : A.R)
    (q : Ideal (𝓞 F)) : ℂ :=
  if h : q ≠ ⊥ ∧ q ⊔ A.cS = ⊤ then σ (A.sexticResidue ⟨q, h⟩ t) else 1

private theorem residue_factor (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (t : A.R) :
    σ (A.sexticResidue I t) =
      ((normalizedFactors I.val).map (primeEval A σ t)).prod := by
  have hall : ∀ (a : Ideal (𝓞 F)) (J : A.Exterior), J.val = a →
      σ (A.sexticResidue J t) =
        ((normalizedFactors J.val).map (primeEval A σ t)).prod := by
    intro a
    induction a using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro J hJ
      exact (J.prop.1 hJ).elim
    | h₂ a ha =>
      intro J hJ
      have ht : J.val = ⊤ := hJ.trans (Ideal.isUnit_iff.mp ha)
      rw [show A.sexticResidue J t = 1 from A.residueValue_top _ J ht t, map_one]
      rw [ht, ← Ideal.one_eq_top, normalizedFactors_one]
      simp
    | h₃ a p ha hp ih =>
      intro J hJ
      have haS : a ⊔ A.cS = ⊤ := by
        apply top_unique
        rw [← J.prop.2]
        apply sup_le_sup_right
        rw [hJ]
        exact Ideal.mul_le_right
      have hpS : p ⊔ A.cS = ⊤ := by
        apply top_unique
        rw [← J.prop.2]
        apply sup_le_sup_right
        rw [hJ]
        exact Ideal.mul_le_left
      let Ia : A.Exterior := ⟨a, ha, haS⟩
      let Ip : A.Exterior := ⟨p, hp.ne_zero, hpS⟩
      rw [show A.sexticResidue J t = A.sexticResidue Ip t * A.sexticResidue Ia t from
        A.sexticResidueFamily_normalized.2.2 Ip Ia J hJ t, map_mul, ih Ia rfl]
      rw [hJ, normalizedFactors_mul hp.ne_zero ha,
        normalizedFactors_irreducible hp.irreducible, normalize_eq,
        Multiset.map_add, Multiset.prod_add, Multiset.map_singleton, Multiset.prod_singleton]
      simp only [primeEval, dif_pos (show p ≠ ⊥ ∧ p ⊔ A.cS = ⊤ from ⟨hp.ne_zero, hpS⟩)]
      rfl
  exact hall I.val I rfl

theorem exteriorSexticRowCharacter_eq_sexticResiduePowerChar
    (A : SArithmeticData F) (σ : F →+* ℂ) (I : A.Exterior) (t : A.R) :
    exteriorSexticRowCharacter A σ I t =
      A.sexticResiduePowerChar σ I 1 (Ideal.Quotient.mk (A.extendIdeal I) t) := by
  by_cases ht : t = 0
  · subst t
    simp only [exteriorSexticRowCharacter, dif_pos rfl]
    by_cases hI : I.val = ⊤
    · rw [if_pos hI, char_one,
        show A.sexticResidue I 0 = 1 from A.residueValue_top _ I hI 0, map_one]
      simp
    · letI : Nontrivial (A.R ⧸ A.extendIdeal I) :=
        Ideal.Quotient.nontrivial_iff.mpr (A.residue_extendIdeal_ne_top I hI)
      rw [if_neg hI, map_zero, A.sexticResiduePowerChar_nonunit σ I 1 0 not_isUnit_zero]
      simp
  · rw [exteriorSexticRowCharacter, dif_neg ht, char_one, residue_factor,
      Finset.prod_multiset_map_count]
    apply Finset.prod_bij (fun p _ => p.val.asIdeal)
    · intro p hp
      simpa only [ThetaBranch.support, Finset.mem_preimage, idealPrimeSupport] using p.property
    · intro p hp q hq he
      apply Subtype.ext
      exact HeightOneSpectrum.asIdeal_injective he
    · intro q hq
      have hf : q ∈ normalizedFactors I.val := Multiset.mem_toFinset.mp hq
      have hqprime := (Ideal.mem_normalizedFactors_iff I.property.1).mp hf |>.1
      let p : HeightOneSpectrum (𝓞 F) := ⟨q, hqprime, (prime_of_normalized_factor q hf).ne_zero⟩
      have hp : p ∈ ThetaBranch.support I.val := by
        simpa only [ThetaBranch.support, Finset.mem_preimage, idealPrimeSupport] using hq
      exact ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩
    · intro p hp
      rw [principal_prime_symbol_eq_sexticResiduePowerChar A σ _ t ht, char_one]
      have he : p.val.asIdeal ≠ ⊥ ∧ p.val.asIdeal ⊔ A.cS = ⊤ :=
        (ThetaBranch.primeIdeal A ⟨p.val, ThetaBranch.support_outside A I p.val p.property⟩).property
      simp only [primeEval, dif_pos he, idealPrimeExponent]
      rfl

theorem PrincipalData.character_eq_sexticResiduePowerChar
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : PrincipalData A σ η hS) (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) (x : FiniteTransform.Residue A.R.toSubring a) :
    P.coefficients.character a x =
      A.sexticResiduePowerChar σ I 1
        (Ideal.quotientEquivAlgOfEq A.R ha.2 x) := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (P.exteriorCharacters I a t ha).trans
    (exteriorSexticRowCharacter_eq_sexticResiduePowerChar A σ I t)

end
end DedekindZetaZeroFree.NormalizedProbe
