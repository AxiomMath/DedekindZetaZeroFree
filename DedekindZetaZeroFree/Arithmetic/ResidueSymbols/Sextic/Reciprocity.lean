module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Hilbert.ProductFormula
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SexticReciprocityAndIdealCharacters

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.ArithmeticContext
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

open AlgebraicNumberTheory.PowerResidueSymbols
set_option backward.isDefEq.respectTransparency false

theorem actual_sextic_prime_integral_cft (A : SArithmeticData F)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hI : I.val = v.asIdeal)
    (hc : (Ideal.absNorm v.asIdeal).Coprime 6)
    (r : 𝓞 F) (hr : r ∉ v.asIdeal) :
    A.sexticResidue I (algebraMap (𝓞 F) A.R r) =
      algebraMap (𝓞 F) F
        ((primeIdealPowerResidueSymbol F v 6 A.primitive_sixth_root hc r hr).val : 𝓞 F) := by
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  letI : I.val.IsMaximal := hI ▸ v.isMaximal
  letI : Field (𝓞 F ⧸ I.val) := Ideal.Quotient.field I.val
  let E := ArithGaussCRT.exteriorQuotientEquiv A I
  let t := primeIdealPowerResidueSymbol F v 6 A.primitive_sixth_root hc r hr
  let u := Units.map E.toMonoidHom
    (Units.mk0 (Ideal.Quotient.mk I.val r) (by
      rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, hI]; exact hr))
  have hu : (u : A.R ⧸ A.extendIdeal I) =
      Ideal.Quotient.mk (A.extendIdeal I) (algebraMap (𝓞 F) A.R r) :=
    ArithGaussCRT.exteriorQuotientEquiv_mk A I r
  obtain ⟨j, hj, hej, hred⟩ := A.sexticResidueFamily_normalized.2.1 I v hI u
  let z := A.primitive_zeta12.toInteger ^ 2
  have hp : IsPrimitiveRoot z 6 := A.primitive_zeta12.toInteger_isPrimitiveRoot.pow
    (by decide) (by decide : 12 = 2 * 6)
  obtain ⟨k, hk, hek⟩ := hp.eq_pow_of_pow_eq_one
    ((mem_rootsOfUnity' 6 t.val).mp t.property)
  have htred : Ideal.Quotient.mk v.asIdeal (t.val : 𝓞 F) =
      Ideal.Quotient.mk v.asIdeal r ^ ((Ideal.absNorm v.asIdeal - 1) / 6) := by
    have ht := rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol
      F v 6 A.primitive_sixth_root hc r hr
    have hh := congrArg (fun q : rootsOfUnity 6 (𝓞 F ⧸ v.asIdeal) =>
      (q.val : 𝓞 F ⧸ v.asIdeal)) ht
    change Ideal.Quotient.mk v.asIdeal (t.val : 𝓞 F) =
      Ideal.Quotient.mk v.asIdeal r ^ ((Fintype.card (𝓞 F ⧸ v.asIdeal) - 1) / 6) at hh
    simpa only [card_primeIdealResidueField] using hh
  have hcard : Nat.card (A.R ⧸ A.extendIdeal I) = Ideal.absNorm v.asIdeal := by
    rw [← hI]
    exact (Nat.card_congr E.toEquiv).symm
  have hredj : Ideal.Quotient.mk v.asIdeal (z ^ j) =
      Ideal.Quotient.mk v.asIdeal r ^ ((Ideal.absNorm v.asIdeal - 1) / 6) := by
    have hh := congrArg E.symm hred
    rw [hcard, hu] at hh
    rw [← ArithGaussCRT.exteriorQuotientEquiv_mk A I,
      ← ArithGaussCRT.exteriorQuotientEquiv_mk A I] at hh
    change E.symm (E (Ideal.Quotient.mk I.val (A.primitive_zeta12.toInteger ^ (2 * j)))) =
      E.symm (E (Ideal.Quotient.mk I.val r) ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) at hh
    rw [E.symm.map_pow, E.symm_apply_apply, E.symm_apply_apply] at hh
    have hh' : Ideal.Quotient.mk v.asIdeal (A.primitive_zeta12.toInteger ^ (2 * j)) =
      Ideal.Quotient.mk v.asIdeal r ^ ((Ideal.absNorm v.asIdeal - 1) / 6) := hI ▸ hh
    simpa only [z, ← pow_mul] using hh'
  have hpq : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal z) 6 :=
    hp.idealQuotient_mk (Ideal.absNorm_eq_one_iff.not.mpr v.isPrime.ne_top) hc
  have hjk : j = k := hpq.pow_inj hj hk (by
    rw [← map_pow, ← map_pow, hek]
    exact hredj.trans htred.symm)
  change MulChar.ofUnitHom (A.sexticResidueFamily I)
    (Ideal.Quotient.mk (A.extendIdeal I) (algebraMap (𝓞 F) A.R r)) = _
  rw [← hu, MulChar.ofUnitHom_coe, hej, ← hek, map_pow, map_pow]
  rw [← hjk]
  change A.zeta12 ^ (2 * j) = (algebraMap (𝓞 F) F A.primitive_zeta12.toInteger ^ 2) ^ j
  change A.zeta12 ^ (2 * j) = ((A.primitive_zeta12.toInteger : F) ^ 2) ^ j
  exact (pow_mul A.zeta12 2 j).trans
    (congrArg (fun x : F => (x ^ 2) ^ j) A.primitive_zeta12.coe_toInteger).symm

open GlobalClassFieldTheory.Reciprocity
open LocalFieldTheory.IsNonarchimedeanLocalField

theorem actual_sextic_local_integral_tame (A : SArithmeticData F)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hI : I.val = v.asIdeal)
    (hc : (Ideal.absNorm v.asIdeal).Coprime 6)
    (hv : v ∉ powerResidueExponentFinitePlaces F 6)
    (r : 𝓞 F) (hr : r ∉ v.asIdeal) (a : Fˣ) :
    ((A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl))
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom
        (primeAvoidingIntegralFieldUnit F v r hr))).val : F) =
      A.sexticResidue I (algebraMap (𝓞 F) A.R r) ^
        (-finitePlaceNormalizedValuation F v a) := by
  have hd := A.actualLocalSymbol_diagonal v 6 (Or.inr (Or.inr rfl)) a
    (primeAvoidingIntegralFieldUnit F v r hr)
  have hd' := congrArg (fun z : rootsOfUnity 6 F => (z.val : F)) hd
  apply hd'.trans
  have hf := ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_finiteFactor
    F 6 (by norm_num) (A.actualHilbert_roots 6 (Or.inr (Or.inr rfl))) v a
      (primeAvoidingIntegralFieldUnit F v r hr)
  change (((ClassFieldTheory.GlobalHilbertPairingFamily.finiteFactor F
    (A.actualRawHilbert 6 (Or.inr (Or.inr rfl)))
    (A.actualHilbert_roots 6 (Or.inr (Or.inr rfl))) v a
      (primeAvoidingIntegralFieldUnit F v r hr))⁻¹).val : F) = _
  have hf' := congrArg (fun z : rootsOfUnity 6 F => ((z⁻¹).val : F)) hf
  apply hf'.trans
  have hs := finitePlaceHilbertSymbol_skew F 6 (by norm_num)
    A.primitive_sixth_root v a (primeAvoidingIntegralFieldUnit F v r hr)
  have ht := finitePlaceHilbertSymbol_eq_primeIdealPowerResidueFactor_zpow F 6
    (by norm_num) A.primitive_sixth_root v hv hc r hr a
  have he := congrArg Inv.inv (hs.trans (congrArg Inv.inv ht))
  simp only [inv_inv] at he
  have he' := congrArg (fun z =>
    (((KummerTheory.nthRootsSubgroupEquivRootsOfUnity F 6) z).val : F)) he
  apply he'.trans
  rw [actual_sextic_prime_integral_cft A I v hI hc r hr]
  have hp := map_zpow (KummerTheory.nthRootsSubgroupEquivRootsOfUnity F 6)
    (integralRootsOfUnityToNthRoots F 6
      (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealPowerResidueSymbol F v 6
        A.primitive_sixth_root hc r hr)) (-finitePlaceNormalizedValuation F v a)
  apply (congrArg (fun z : rootsOfUnity 6 F => (z.val : F)) hp).trans
  simp only [Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val]
  rfl

theorem actual_sextic_local_sinteger_tame (A : SArithmeticData F)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hI : I.val = v.asIdeal)
    (hc : (Ideal.absNorm v.asIdeal).Coprime 6)
    (hv : v ∉ powerResidueExponentFinitePlaces F 6) (hvS : v ∉ A.Sf)
    (b : A.R) (ub : Fˣ) (hub : (ub : F) = (b : F))
    (hval : v.valuation F (ub : F) = 1) (a : Fˣ) :
    ((A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl))
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom ub)).val : F) =
      A.sexticResidue I b ^ (-finitePlaceNormalizedValuation F v a) := by
  obtain ⟨n, d, hd⟩ := v.exists_primeCompl_mul_eq_of_integer (b : F) (b.property v hvS)
  have hdn : (d : 𝓞 F) ∉ v.asIdeal := d.property
  have hdv : v.valuation F ((d : 𝓞 F) : F) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F)).mpr hdn
  have hnv : v.valuation F (n : F) = 1 := by
    have hd' : (b : F) * ((d : 𝓞 F) : F) = (n : F) := hd
    rw [← hd', map_mul, ← hub, hval, hdv, one_mul]
  have hnn : n ∉ v.asIdeal := (v.valuation_eq_one_iff_notMem (K := F)).mp hnv
  let ud := primeAvoidingIntegralFieldUnit F v d hdn
  let un := primeAvoidingIntegralFieldUnit F v n hnn
  have hmul : ub * ud = un := by
    apply Units.ext
    change (ub : F) * ((d : 𝓞 F) : F) = (n : F)
    rw [hub]
    exact hd
  have hchars : A.sexticResidue I b *
      A.sexticResidue I (algebraMap (𝓞 F) A.R d) =
      A.sexticResidue I (algebraMap (𝓞 F) A.R n) := by
    have he : b * algebraMap (𝓞 F) A.R d = algebraMap (𝓞 F) A.R n := by
      apply Subtype.ext
      exact hd
    change MulChar.ofUnitHom (A.sexticResidueFamily I) (Ideal.Quotient.mk (A.extendIdeal I) b) *
      MulChar.ofUnitHom (A.sexticResidueFamily I) (Ideal.Quotient.mk (A.extendIdeal I) (algebraMap (𝓞 F) A.R d)) = _
    rw [← map_mul, ← map_mul, he]
    rfl
  have hbmul : A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl))
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom un) =
    A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl))
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom ub) *
    A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl))
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom ud) := by
    rw [← hmul]
    simp only [SArithmeticData.actualLocalSymbol, map_mul]
  have he := congrArg (fun z : rootsOfUnity 6 F => (z.val : F)) hbmul
  have hnt := actual_sextic_local_integral_tame A I v hI hc hv n hnn a
  have hdt := actual_sextic_local_integral_tame A I v hI hc hv d hdn a
  change _ = _ * _ at he
  rw [hnt, hdt, ← hchars, mul_zpow] at he
  have hnzero : A.sexticResidue I (algebraMap (𝓞 F) A.R d) ≠ 0 := by
    rw [actual_sextic_prime_integral_cft A I v hI hc d hdn]
    exact (Units.map (algebraMap (𝓞 F) F).toMonoidHom
      (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealPowerResidueSymbol F v 6
        A.primitive_sixth_root hc d hdn).val).ne_zero
  exact (mul_right_cancel₀ (zpow_ne_zero _ hnzero) he).symm

theorem actual_sextic_top (A : SArithmeticData F) (I : A.Exterior)
    (hI : I.val = ⊤) (x : A.R) : A.sexticResidue I x = 1 :=
  A.residueValue_top A.sexticResidueFamily I hI x

theorem actual_sextic_nonunit (A : SArithmeticData F) (I : A.Exterior) (x : A.R)
    (hx : ¬ IsUnit (Ideal.Quotient.mk (A.extendIdeal I) x)) :
    A.sexticResidue I x = 0 := MulChar.map_nonunit _ hx

open UniqueFactorizationMonoid

theorem actual_sextic_factorization (A : SArithmeticData F) (x : A.R)
    (f : Ideal (𝓞 F) → F)
    (hf : ∀ (P : A.Exterior) (v : HeightOneSpectrum (𝓞 F)),
      P.val = v.asIdeal → f P.val = A.sexticResidue P x)
    (I : A.Exterior) :
    A.sexticResidue I x = ((normalizedFactors I.val).map f).prod := by
  have hall : ∀ (a : Ideal (𝓞 F)) (J : A.Exterior), J.val = a →
      A.sexticResidue J x = ((normalizedFactors J.val).map f).prod := by
    intro a
    induction a using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro J hJ
      exact (J.prop.1 hJ).elim
    | h₂ a ha =>
      intro J hJ
      have ht : J.val = ⊤ := hJ.trans (Ideal.isUnit_iff.mp ha)
      rw [actual_sextic_top A J ht, ht]
      rw [← Ideal.one_eq_top, normalizedFactors_one, Multiset.map_zero, Multiset.prod_zero]
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
      have hmul := A.sexticResidueFamily_normalized.2.2 Ip Ia J hJ x
      change A.sexticResidue J x = A.sexticResidue Ip x * A.sexticResidue Ia x at hmul
      rw [hmul, ih Ia rfl, ← hf Ip (HeightOneSpectrum.ofPrime hp) rfl,
        hJ, normalizedFactors_mul hp.ne_zero ha]
      have hpone : normalizedFactors p = {p} := by
        simpa only [normalize_eq] using normalizedFactors_irreducible hp.irreducible
      rw [hpone]
      change f p * ((normalizedFactors a).map f).prod = _
      simp
  exact hall I.val I rfl

theorem actual_sextic_factorization_finprod (A : SArithmeticData F) (x : A.R)
    (g : HeightOneSpectrum (𝓞 F) → F)
    (hg : ∀ (P : A.Exterior) (v : HeightOneSpectrum (𝓞 F)),
      P.val = v.asIdeal → g v = A.sexticResidue P x)
    (I : A.Exterior) :
    A.sexticResidue I x = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      g v ^ idealPrimeExponent v.asIdeal I.val := by
  let f : Ideal (𝓞 F) → F := fun q => if h : q.IsPrime ∧ q ≠ ⊥ then
    g ⟨q, h.1, h.2⟩ else 1
  have hf : ∀ (P : A.Exterior) (v : HeightOneSpectrum (𝓞 F)),
      P.val = v.asIdeal → f P.val = A.sexticResidue P x := by
    intro P v hP
    have hq : P.val.IsPrime ∧ P.val ≠ ⊥ := ⟨hP ▸ v.isPrime, P.property.1⟩
    dsimp [f]
    rw [dif_pos hq]
    have he : (⟨P.val, hq.1, hq.2⟩ : HeightOneSpectrum (𝓞 F)) = v := by
      exact HeightOneSpectrum.ext hP
    rw [he]
    exact hg P v hP
  rw [actual_sextic_factorization A x f hf I, Multiset.prod_map_eq_finprod]
  let e : HeightOneSpectrum (𝓞 F) ↪ Ideal (𝓞 F) := ⟨fun v => v.asIdeal, by
    intro v w h
    exact HeightOneSpectrum.ext h⟩
  have he := finprod_emb_domain e (fun v => g v ^ idealPrimeExponent v.asIdeal I.val)
  apply Eq.trans _ he
  apply finprod_congr
  intro q
  by_cases hq : q ∈ Set.range e
  · obtain ⟨v, hv⟩ := hq
    subst q
    have hn : v.asIdeal.IsPrime ∧ v.asIdeal ≠ ⊥ := ⟨v.isPrime, v.ne_bot⟩
    change f v.asIdeal ^ (normalizedFactors I.val).count v.asIdeal = _
    rw [dif_pos (Set.mem_range_self v)]
    have hc := e.injective (Classical.choose_spec (Set.mem_range_self v))
    rw [hc]
    change (if h : v.asIdeal.IsPrime ∧ v.asIdeal ≠ ⊥ then
      g ⟨v.asIdeal, h.1, h.2⟩ else 1) ^ _ = _
    rw [dif_pos hn]
    rfl
  · have hn : ¬ (q.IsPrime ∧ q ≠ ⊥) := by
      intro h
      exact hq ⟨⟨q, h.1, h.2⟩, rfl⟩
    simp [f, hn, hq]

theorem actual_exterior_prime_outside (A : SArithmeticData F) (I : A.Exterior)
    (v : HeightOneSpectrum (𝓞 F)) (hI : I.val = v.asIdeal) : v ∉ A.Sf := by
  intro hv
  have h := (A.exterior_iff ⟨I.val, I.property.1⟩).mp I.property.2 v hv
  rw [hI, sup_idem] at h
  exact v.isPrime.ne_top h

theorem actual_outside_norm_coprime_six (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    (Ideal.absNorm v.asIdeal).Coprime 6 := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨p,n,hn,hpI,hp,hq⟩ := Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
  rw [hq]
  apply Nat.Coprime.pow_left
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  apply hv
  obtain ⟨k,hk⟩ := hd
  apply A.above_six
  have hd' : (p : 𝓞 F) ∣ 6 := ⟨(k : 𝓞 F), by exact_mod_cast hk⟩
  exact Ideal.mem_of_dvd v.asIdeal hd' hpI

theorem actual_outside_exponent_support (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    v ∉ powerResidueExponentFinitePlaces F 6 := by
  intro h
  rw [mem_powerResidueExponentFinitePlaces_iff, Ideal.dvd_iff_le] at h
  apply hv
  apply A.above_six
  exact (Ideal.span_singleton_le_iff_mem _).mp h

 def generatorBoundIdeal (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) (n : ℕ) : Ideal A.R where
  carrier := {a | v.valuation F (a : F) ≤ WithZero.exp (-(n : ℤ))}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change v.valuation F ((a : F) + (b : F)) ≤ _
    exact (ValuationClass.map_add_le_max _ _ _).trans (max_le ha hb)
  smul_mem' := by
    intro a b hb
    change v.valuation F ((a : F) * (b : F)) ≤ _
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (a.property v hv) zero_le).trans (by simpa using hb)

theorem actual_generator_valuation (A : SArithmeticData F)
    (I : A.Exterior) (r : A.R) (hr : A.Generates I r) (a : Fˣ) (ha : (a : F) = (r : F))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    v.valuation F (a : F) =
      WithZero.exp (-(idealPrimeExponent v.asIdeal I.val : ℤ)) := by
  classical
  let n := idealPrimeExponent v.asIdeal I.val
  have hdvd (k : ℕ) : v.asIdeal ^ k ∣ I.val ↔ k ≤ n := by
    rw [pow_dvd_iff_le_emultiplicity,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible I.property.1]
    simp [n, idealPrimeExponent]
  have hIn : I.val ≤ v.asIdeal ^ n := Ideal.dvd_iff_le.mp ((hdvd n).mpr le_rfl)
  have hnot : ¬ I.val ≤ v.asIdeal ^ (n + 1) := by
    rw [← Ideal.dvd_iff_le, hdvd]; omega
  have hmap : A.extendIdeal I ≤ generatorBoundIdeal A v hv n := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change v.valuation F (b : F) ≤ WithZero.exp (-(n : ℤ))
    rw [v.valuation_of_algebraMap]
    exact (v.intValuation_le_pow_iff_mem b n).mpr (hIn hb)
  have hrv : v.valuation F (r : F) ≤ WithZero.exp (-(n : ℤ)) := by
    apply hmap
    rw [← hr.2]
    exact Ideal.subset_span (Set.mem_singleton r)
  obtain ⟨b, hb, hbn⟩ : ∃ b : 𝓞 F, b ∈ I.val ∧ b ∉ v.asIdeal ^ (n + 1) := by
    contrapose! hnot
    exact hnot
  have hbm : algebraMap (𝓞 F) A.R b ∈ Ideal.span ({r} : Set A.R) := by
    rw [hr.2]
    exact Ideal.mem_map_of_mem _ hb
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hbm
  have hbv : v.valuation F (b : F) ≤ v.valuation F (r : F) := by
    have hh := congrArg (fun t : A.R => (t : F)) hy
    change (b : F) = (r : F) * (y : F) at hh
    rw [hh, map_mul]
    exact (mul_le_mul_of_nonneg_left (y.property v hv) zero_le).trans (by simp)
  have hrv' : ¬ v.valuation F (r : F) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    intro h
    apply hbn
    apply (v.intValuation_le_pow_iff_mem b (n + 1)).mp
    rw [← v.valuation_of_algebraMap (K := F)]
    exact hbv.trans h
  have hnz : v.valuation F (r : F) ≠ 0 := by
    rw [← ha]
    exact (Valuation.ne_zero_iff _).mpr a.ne_zero
  rw [← WithZero.exp_log hnz, WithZero.exp_le_exp] at hrv hrv'
  have he : WithZero.log (v.valuation F (r : F)) = -(n : ℤ) := by
    push_cast at hrv'
    omega
  rw [ha, ← WithZero.exp_log hnz, he]

private theorem cft_valuation_mul (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) :
    finitePlaceNormalizedValuation F v (a*b) =
      finitePlaceNormalizedValuation F v a + finitePlaceNormalizedValuation F v b := by
  unfold finitePlaceNormalizedValuation finitePlaceHilbert_completionUnit
  simp only [map_mul]
  rw [valuationMap_ofMul_mul]

theorem actual_generator_cft_exponent (A : SArithmeticData F)
    (I : A.Exterior) (r : A.R) (hr : A.Generates I r) (a : Fˣ) (ha : (a : F) = (r : F))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    -finitePlaceNormalizedValuation F v a = (idealPrimeExponent v.asIdeal I.val : ℤ) := by
  obtain ⟨n,d,hd⟩ := v.exists_primeCompl_mul_eq_of_integer (r : F) (r.property v hv)
  have hdv : v.valuation F ((d : 𝓞 F) : F) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F)).mpr d.property
  have hn : n ≠ 0 := by
    intro hn
    have he : (a : F) * ((d : 𝓞 F) : F) = 0 := by simpa [ha, hn] using hd
    rcases mul_eq_zero.mp he with he | he
    · exact a.ne_zero he
    · have hz : v.valuation F ((d : 𝓞 F) : F) = 0 := by rw [he, map_zero]
      exact zero_ne_one (hz.symm.trans hdv)
  let un := nonzeroIntegralFieldUnit F n hn
  let ud := primeAvoidingIntegralFieldUnit F v d d.property
  have heU : a * ud = un := by
    apply Units.ext
    change (a : F) * ((d : 𝓞 F) : F) = (n : F)
    rw [ha]
    exact hd
  have heN := cft_valuation_mul v a ud
  rw [heU] at heN
  dsimp only [un, ud] at heN
  rw [finitePlaceNormalizedValuation_primeAvoidingIntegralFieldUnit] at heN
  have hd' : (r : F) * ((d : 𝓞 F) : F) = (n : F) := hd
  have hvn : v.valuation F (n : F) = v.valuation F (a : F) := by
    rw [← hd', map_mul, ← ha, hdv, mul_one]
  have hexp := actual_generator_valuation A I r hr a ha v hv
  have hexp' := intValuation_eq_exp_neg_idealPrimeMultiplicity F v n hn
  have hm : (AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity F v (Ideal.span {n}) : ℤ) =
      (idealPrimeExponent v.asIdeal I.val : ℤ) := by
    apply neg_injective
    apply WithZero.exp_injective
    rw [← hexp', ← v.valuation_of_algebraMap (K := F)]
    exact hvn.trans hexp
  rw [finitePlaceNormalizedValuation_nonzeroIntegralFieldUnit] at heN
  have hdz : -(AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity F v
      (Ideal.span {(d : 𝓞 F)}) : ℤ) = 0 := by
    apply WithZero.exp_injective
    rw [← intValuation_eq_exp_neg_idealPrimeMultiplicity F v d
      (by intro h; exact d.property (h ▸ Ideal.zero_mem _)), WithZero.exp_zero]
    rw [← v.valuation_of_algebraMap (K := F)]
    exact hdv
  rw [hm, hdz] at heN
  omega

theorem actual_generator_valuation_unit (A : SArithmeticData F)
    (J : A.Exterior) (b : A.R) (ub : Fˣ) (hb : A.Generates J b)
    (hub : (ub : F) = (b : F)) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ A.Sf) (hnot : ¬ J.val ≤ v.asIdeal) :
    v.valuation F (ub : F) = 1 := by
  obtain ⟨t,ht,htv⟩ := SetLike.not_le_iff_exists.mp hnot
  have htR : algebraMap (𝓞 F) A.R t ∈ Ideal.span {b} := by
    rw [hb.2]
    exact Ideal.mem_map_of_mem _ ht
  obtain ⟨y,hy⟩ := Ideal.mem_span_singleton.mp htR
  have he : (t : F) = (b : F) * (y : F) := congrArg (fun z : A.R => (z : F)) hy
  have htval : v.valuation F (t : F) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).mpr htv
  rw [hub]
  apply le_antisymm (b.property v hv)
  rw [← htval, he, map_mul]
  exact (mul_le_mul_of_nonneg_left (y.property v hv) zero_le).trans (by simp)

open scoped nonZeroDivisors

private theorem normalized_int (v : HeightOneSpectrum (𝓞 F)) (n : 𝓞 F) (hn : n ≠ 0) :
    finitePlaceNormalizedValuation F v (nonzeroIntegralFieldUnit F n hn) =
      WithZero.log (v.valuation F (n : F)) := by
  rw [finitePlaceNormalizedValuation_nonzeroIntegralFieldUnit]
  have he := intValuation_eq_exp_neg_idealPrimeMultiplicity F v n hn
  have he' : v.valuation F (n : F) = _ := (v.valuation_of_algebraMap n).trans he
  rw [he', WithZero.log_exp]

theorem actual_cft_normalizedValuation_log (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    finitePlaceNormalizedValuation F v a = WithZero.log (v.valuation F (a : F)) := by
  obtain ⟨n, d, hd⟩ := IsFractionRing.div_surjective (𝓞 F) (a : F)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd.1
  have hn : n ≠ 0 := by
    intro h
    have hh := hd.2
    rw [h, map_zero, zero_div] at hh
    exact a.ne_zero hh.symm
  let un := nonzeroIntegralFieldUnit F n hn
  let ud := nonzeroIntegralFieldUnit F d hd0
  have ha : a = un / ud := by
    apply Units.ext
    rw [Units.val_div_eq_div_val]
    exact hd.2.symm
  have hvn : v.valuation F (n : F) ≠ 0 := by
    apply (Valuation.ne_zero_iff _).mpr
    exact (nonzeroIntegralFieldUnit F n hn).ne_zero
  have hvd : v.valuation F ((d : 𝓞 F) : F) ≠ 0 := by
    apply (Valuation.ne_zero_iff _).mpr
    exact (nonzeroIntegralFieldUnit F d hd0).ne_zero
  rw [ha]
  have hv : finitePlaceNormalizedValuation F v (un / ud) =
      finitePlaceNormalizedValuation F v un - finitePlaceNormalizedValuation F v ud := by
    unfold finitePlaceNormalizedValuation finitePlaceHilbert_completionUnit
    simp only [map_div]
    exact LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_ofMul_div _ _ _
  rw [hv, normalized_int v n hn, normalized_int v d hd0]
  rw [Units.val_div_eq_div_val]
  change _ = WithZero.log (v.valuation F ((n : F) / (d : F)))
  rw [map_div₀, WithZero.log_div hvn hvd]

 def factor (A : SArithmeticData F) (a b : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) : F :=
  ((A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl))
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b)).val : F)
private theorem globalprod (A : SArithmeticData F) (a b : Fˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 F), factor A a b v) = 1 := by
  let g : rootsOfUnity 6 F →* F := (Units.coeHom F).comp (rootsOfUnity 6 F).subtype
  have hg : Function.Injective g := by
    intro x y h
    exact Subtype.ext (Units.ext h)
  have h := g.map_finprod_of_injective hg (fun v : HeightOneSpectrum (𝓞 F) =>
    A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl))
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b))
  have hp := A.actualSextic_productFormula a b
  exact h.symm.trans ((congrArg g hp).trans (map_one g))
private theorem split_product (A : SArithmeticData F) (a b : Fˣ)
    (hf : (factor A a b).HasFiniteMulSupport) :
    ((A.H_S (A.diagonal a) (A.diagonal b)).val : F) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 F), ∏ᶠ (_ : v ∉ (A.Sf : Set _)),
        factor A a b v) = 1 := by
  have hs : ((A.H_S (A.diagonal a) (A.diagonal b)).val : F) =
      ∏ᶠ v ∈ (A.Sf : Set _), factor A a b v := by
    rw [finprod_mem_coe_finset]
    have hsroot : A.H_S (A.diagonal a) (A.diagonal b) =
      ∏ v ∈ A.Sf, A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl))
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b) :=
      Finset.prod_coe_sort A.Sf (fun v => A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl))
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b))
    have hv := congrArg ((Units.coeHom F).comp (rootsOfUnity 6 F).subtype) hsroot
    have hm := map_prod ((Units.coeHom F).comp (rootsOfUnity 6 F).subtype)
      (fun v => A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl))
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b)) A.Sf
    exact hv.trans hm
  rw [hs]
  have he := finprod_mem_mul_sdiff' (f := factor A a b)
    (s := (A.Sf : Set _)) (t := Set.univ) (Set.subset_univ _) (by rw [Set.univ_inter]; exact hf)
  rw [finprod_mem_univ] at he
  simpa only [Set.mem_diff, Set.mem_univ, true_and] using
    he.trans (globalprod A a b)

private theorem actual_factor_finiteSupport (A : SArithmeticData F) (a b : Fˣ) :
    (factor A a b).HasFiniteMulSupport := by
  open GlobalClassFieldTheory.Reciprocity in
  let S := powerResidueBadFinitePlaces F 6 a b
  apply Set.Finite.subset (Finset.finite_toSet S)
  intro v hv
  by_contra hn
  have hh := GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol_eq_one_of_not_mem_powerResidueBadFinitePlaces
    F 6 (by norm_num) A.primitive_sixth_root a b v hn
  have hd := A.actualLocalSymbol_diagonal v 6 (Or.inr (Or.inr rfl)) a b
  have hf := ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_finiteFactor
    F 6 (by norm_num) (A.actualHilbert_roots 6 (Or.inr (Or.inr rfl))) v a b
  have hf' : ClassFieldTheory.globalFinitePlaceHilbertSymbol F 6 (by norm_num)
    A.primitive_sixth_root v a b = 1 :=
      (congrArg (KummerTheory.nthRootsSubgroupEquivRootsOfUnity F 6) hh).trans (map_one _)
  have hz := hd.trans (congrArg Inv.inv (hf.trans hf'))
  apply hv
  exact (congrArg (fun z : rootsOfUnity 6 F => (z.val : F)) hz).trans (by rfl)

 theorem outside_exterior (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) : v.asIdeal ⊔ A.cS = ⊤ := by
  apply Ideal.sup_prod_eq_top
  intro w hw
  have hne : v ≠ w := fun he => hv (he ▸ hw)
  have hin : v.asIdeal ≠ w.asIdeal := fun he => hne (HeightOneSpectrum.ext he)
  exact Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal hin
 def primeValue (A : SArithmeticData F) (x : A.R) (v : HeightOneSpectrum (𝓞 F)) : F :=
  if hv : v ∉ A.Sf then A.sexticResidue ⟨v.asIdeal, v.ne_bot, outside_exterior A v hv⟩ x else 1
private theorem primeval (A : SArithmeticData F) (x : A.R)
    (P : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hP : P.val = v.asIdeal) :
    primeValue A x v = A.sexticResidue P x := by
  have hv := actual_exterior_prime_outside A P v hP
  rw [primeValue, dif_pos hv]
  congr 1
  exact Subtype.ext hP.symm
private theorem residue_prod (A : SArithmeticData F) (I : A.Exterior) (x : A.R) :
    A.sexticResidue I x = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      primeValue A x v ^ idealPrimeExponent v.asIdeal I.val :=
    actual_sextic_factorization_finprod A x (primeValue A x) (primeval A x) I
private theorem exponent_support (I : Ideal (𝓞 F)) :
    (fun v : HeightOneSpectrum (𝓞 F) => idealPrimeExponent v.asIdeal I).support.Finite := by
  have he : Function.Injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) := by
    intro v w h
    exact HeightOneSpectrum.ext h
  have hf := (idealPrimeSupport I).finite_toSet.preimage he.injOn
  apply hf.subset
  intro v hv
  change v.asIdeal ∈ idealPrimeSupport I
  exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero hv))
private theorem power_finite (A : SArithmeticData F) (I : A.Exterior) (x : A.R) :
    (fun v : HeightOneSpectrum (𝓞 F) =>
      primeValue A x v ^ idealPrimeExponent v.asIdeal I.val).HasFiniteMulSupport := by
  apply (exponent_support I.val).subset
  intro v hv
  change idealPrimeExponent v.asIdeal I.val ≠ 0
  intro h
  exact hv (by change primeValue A x v ^ idealPrimeExponent v.asIdeal I.val = 1; exact h ▸ pow_zero _)

private theorem coprime_wrapper (A : SArithmeticData F)
    (I J : A.Exterior) (a b : A.R) (ua ub : Fˣ)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      factor A ua ub v = (primeValue A b v ^ idealPrimeExponent v.asIdeal I.val) *
        (primeValue A a v ^ idealPrimeExponent v.asIdeal J.val)⁻¹) :
    A.sexticResidue I b =
      (((A.H_S (A.diagonal ua) (A.diagonal ub))⁻¹ : Fˣ) : F) *
        A.sexticResidue J a := by
  have hglobal := split_product A ua ub (actual_factor_finiteSupport A ua ub)
  have hout : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ∏ᶠ (_ : v ∉ (A.Sf : Set _)),
      factor A ua ub v) = A.sexticResidue I b * (A.sexticResidue J a)⁻¹ := by
    have he : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ∏ᶠ (_ : v ∉ (A.Sf : Set _)),
        factor A ua ub v) = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
          (primeValue A b v ^ idealPrimeExponent v.asIdeal I.val) *
            (primeValue A a v ^ idealPrimeExponent v.asIdeal J.val)⁻¹ := by
      apply finprod_congr
      intro v
      by_cases hv : v ∉ (A.Sf : Set _)
      · rw [finprod_eq_if, if_pos hv]
        exact hloc v hv
      · rw [finprod_eq_if, if_neg hv]
        have hin : v ∈ A.Sf := Classical.byContradiction hv
        simp [primeValue, hin]
    rw [he, finprod_mul_distrib (power_finite A I b) (power_finite A J a).fun_inv,
      finprod_inv_distrib, ← residue_prod A I b, ← residue_prod A J a]
  rw [hout] at hglobal
  have hJ : A.sexticResidue J a ≠ 0 := by
    intro hz
    rw [hz, inv_zero, mul_zero, mul_zero] at hglobal
    exact zero_ne_one hglobal
  have hHS : ((A.H_S (A.diagonal ua) (A.diagonal ub)).val : F) ≠ 0 :=
    (A.H_S (A.diagonal ua) (A.diagonal ub)).val.ne_zero
  rw [Units.val_inv_eq_inv_val]
  field_simp
  field_simp at hglobal
  linear_combination hglobal
private theorem sunit_wrapper (A : SArithmeticData F)
    (I : A.Exterior) (ua : Fˣ) (eps : A.U)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      factor A ua eps.val v = primeValue A (A.unitEquiv eps : A.R) v ^
        idealPrimeExponent v.asIdeal I.val) :
    A.sexticResidue I (A.unitEquiv eps : A.R) =
      ((A.H_S (A.diagonal eps.val) (A.diagonal ua) : Fˣ) : F) := by
  have hglobal := split_product A ua eps.val (actual_factor_finiteSupport A ua eps.val)
  have hout : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ∏ᶠ (_ : v ∉ (A.Sf : Set _)),
      factor A ua eps.val v) = A.sexticResidue I (A.unitEquiv eps : A.R) := by
    rw [residue_prod]
    apply finprod_congr
    intro v
    by_cases hv : v ∉ (A.Sf : Set _)
    · rw [finprod_eq_if, if_pos hv]
      exact hloc v hv
    · rw [finprod_eq_if, if_neg hv]
      have hin : v ∈ A.Sf := Classical.byContradiction hv
      simp [primeValue, hin]
  rw [hout] at hglobal
  have hHS : ((A.H_S (A.diagonal ua) (A.diagonal eps.val)).val : F) ≠ 0 :=
    (A.H_S (A.diagonal ua) (A.diagonal eps.val)).val.ne_zero
  have hs := A.H_S_skew (A.diagonal eps.val) (A.diagonal ua)
  have he := congrArg (fun z : rootsOfUnity 6 F => (z.val : F)) hs
  simp only [Subgroup.coe_inv, Units.val_inv_eq_inv_val] at he
  apply Eq.trans _ he.symm
  field_simp
  simpa only [mul_comm] using hglobal

theorem actual_sextic_sunit_symbol_of_cft_exponents (A : SArithmeticData F)
    (I : A.Exterior) (ua : Fˣ) (eps : A.U)
    (hexp : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      -finitePlaceNormalizedValuation F v ua = (idealPrimeExponent v.asIdeal I.val : ℤ)) :
    A.sexticResidue I (A.unitEquiv eps : A.R) =
      ((A.H_S (A.diagonal eps.val) (A.diagonal ua) : Fˣ) : F) := by
  apply sunit_wrapper
  intro v hv
  let P : A.Exterior := ⟨v.asIdeal, v.ne_bot, outside_exterior A v hv⟩
  have hval : v.valuation F (eps.val : F) = 1 := eps.property v hv
  have ht := actual_sextic_local_sinteger_tame A P v rfl
    (actual_outside_norm_coprime_six A v hv) (actual_outside_exponent_support A v hv)
    hv (A.unitEquiv eps : A.R) eps.val rfl hval ua
  rw [hexp v hv, zpow_natCast] at ht
  have hp : primeValue A (A.unitEquiv eps : A.R) v =
      A.sexticResidue P (A.unitEquiv eps : A.R) := by
    exact primeval A _ P v rfl
  exact ht.trans (congrArg (fun z => z ^ idealPrimeExponent v.asIdeal I.val) hp.symm)

private lemma generator_unit_of_exponent_zero (A : SArithmeticData F)
    (I : A.Exterior) (r : A.R) (hr : A.Generates I r) (a : Fˣ)
    (ha : (a : F) = (r : F)) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf)
    (he : idealPrimeExponent v.asIdeal I.val = 0) : v.valuation F (a : F) = 1 := by
  have h := actual_generator_cft_exponent A I r hr a ha v hv
  rw [actual_cft_normalizedValuation_log, he, Nat.cast_zero] at h
  have hz : WithZero.log (v.valuation F (a : F)) = 0 := neg_eq_zero.mp h
  have hn : v.valuation F (a : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
  rw [← WithZero.exp_log hn, hz, WithZero.exp_zero]
private lemma coprime_exponents (A : SArithmeticData F) (I J : A.Exterior)
    (hcop : I.val ⊔ J.val = ⊤) (v : HeightOneSpectrum (𝓞 F)) :
    idealPrimeExponent v.asIdeal I.val = 0 ∨ idealPrimeExponent v.asIdeal J.val = 0 := by
  by_contra h
  push Not at h
  have hi : I.val ≤ v.asIdeal :=
    ((Ideal.mem_normalizedFactors_iff I.property.1).mp
      (Multiset.count_pos.mp (Nat.pos_of_ne_zero h.1))).2
  have hj : J.val ≤ v.asIdeal :=
    ((Ideal.mem_normalizedFactors_iff J.property.1).mp
      (Multiset.count_pos.mp (Nat.pos_of_ne_zero h.2))).2
  exact v.isPrime.ne_top (top_unique (hcop ▸ sup_le hi hj))
private theorem coprime_local (A : SArithmeticData F)
    (I J : A.Exterior) (a b : A.R) (ua ub : Fˣ)
    (ha : A.Generates I a) (hb : A.Generates J b)
    (hua : (ua : F) = (a : F)) (hub : (ub : F) = (b : F))
    (hcop : I.val ⊔ J.val = ⊤) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
      factor A ua ub v = (primeValue A b v ^ idealPrimeExponent v.asIdeal I.val) *
        (primeValue A a v ^ idealPrimeExponent v.asIdeal J.val)⁻¹ := by
  let P : A.Exterior := ⟨v.asIdeal, v.ne_bot, outside_exterior A v hv⟩
  have hp (x : A.R) : primeValue A x v = A.sexticResidue P x := primeval A x P v rfl
  have hc := actual_outside_norm_coprime_six A v hv
  have hs := actual_outside_exponent_support A v hv
  rcases coprime_exponents A I J hcop v with hi | hj
  · have hvu := generator_unit_of_exponent_zero A I a ha ua hua v hv hi
    have ht := actual_sextic_local_sinteger_tame A P v rfl hc hs hv a ua hua hvu ub
    rw [actual_generator_cft_exponent A J b hb ub hub v hv, zpow_natCast] at ht
    have hsk := A.actualLocalHilbert_skew v 6 (Or.inr (Or.inr rfl))
      (QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) 6).range
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom ua))
      (QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) 6).range
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom ub))
    have hsk' := congrArg (fun z : rootsOfUnity 6 F => (z.val : F)) hsk
    simp only [Subgroup.coe_inv, Units.val_inv_eq_inv_val] at hsk'
    change factor A ua ub v = (factor A ub ua v)⁻¹ at hsk'
    rw [hsk', hi, pow_zero, one_mul, hp a]
    exact congrArg Inv.inv ht
  · have hvu := generator_unit_of_exponent_zero A J b hb ub hub v hv hj
    have ht := actual_sextic_local_sinteger_tame A P v rfl hc hs hv b ub hub hvu ua
    rw [actual_generator_cft_exponent A I a ha ua hua v hv, zpow_natCast] at ht
    rw [hj, pow_zero, inv_one, mul_one, hp b]
    exact ht

theorem actual_sextic_coprime_reciprocity (A : SArithmeticData F)
    (I J : A.Exterior) (a b : A.R) (ua ub : Fˣ)
    (ha : A.Generates I a) (hb : A.Generates J b)
    (hua : (ua : F) = (a : F)) (hub : (ub : F) = (b : F))
    (hcop : I.val ⊔ J.val = ⊤) :
    A.sexticResidue I b =
      (((A.H_S (A.diagonal ua) (A.diagonal ub))⁻¹ : Fˣ) : F) *
        A.sexticResidue J a := by
  apply coprime_wrapper
  intro v hv
  exact coprime_local A I J a b ua ub ha hb hua hub hcop v hv

theorem actual_sextic_sunit_symbol (A : SArithmeticData F)
    (I : A.Exterior) (a : A.R) (ua : Fˣ) (eps : A.U)
    (ha : A.Generates I a) (hua : (ua : F) = (a : F)) :
    A.sexticResidue I (A.unitEquiv eps : A.R) =
      ((A.H_S (A.diagonal eps.val) (A.diagonal ua) : Fˣ) : F) := by
  apply actual_sextic_sunit_symbol_of_cft_exponents
  intro v hv
  exact actual_generator_cft_exponent A I a ha ua hua v hv

end
end DedekindZetaZeroFree.ArithmeticContext
