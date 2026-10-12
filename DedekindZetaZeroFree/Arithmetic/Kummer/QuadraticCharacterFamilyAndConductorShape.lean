module

public import DedekindZetaZeroFree.Arithmetic.Kummer.TameQuadraticConductorExponents
public import DedekindZetaZeroFree.Arithmetic.Kummer.CubicSexticExteriorValues
public import DedekindZetaZeroFree.Arithmetic.Kummer.TotalQuadraticCharacterFamily
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveCharactersByCRT

@[expose] public section

section

namespace DedekindZetaZeroFree.RMKummerConductorArithmetic
noncomputable section
open scoped NumberField Classical WithZero
open IsDedekindDomain UniqueFactorizationMonoid
variable {F : Type} [Field F] [NumberField F]

theorem generator_radicalOrder (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (c : Ideal (𝓞 F)) (hc : Squarefree c)
    (hcop : c ⊔ uniformSquareUnitModulus A.Sf = ⊤)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    RMTameQuadraticExponent.radicalOrder F v
      (KummerSquarefreeMembers.generator A σ η hS C c hc hcop) =
        (idealPrimeExponent v.asIdeal c : ℤ) := by
  let a := KummerSquarefreeMembers.chooseRepresentative A σ η hS C
    (KummerSquarefreeMembers.exteriorIndex A c hc hcop)
  have h := SIntegerLocalization.generator_valuation A.Sf c hc.ne_zero
    a.integral a.generates.1 a.generates.2 v hv
  change -WithZero.log (v.valuation F (a.radical : F)) = _
  rw [a.radical_eq, h, WithZero.log_exp, neg_neg]

theorem residue_odd_outside (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    ringChar (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ≠ 2 := by
  have htwo : (2 : 𝓞 F) ∉ v.asIdeal := by
    intro h
    apply hv (A.above_six v ?_)
    convert v.asIdeal.mul_mem_left 3 h using 1 <;> norm_num
  have hval : v.valuation F (2 : F) = 1 := by
    convert (v.valuation_eq_one_iff_notMem (K := F) (r := (2 : 𝓞 F))).2 htwo
      using 1 <;> norm_cast
  have hunit : IsUnit (2 : v.adicCompletionIntegers F) := by
    apply (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.valuationSubring.integers Valued.v)).mpr
    change Valued.v (2 : v.adicCompletion F) = 1
    rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 2]
    exact (HeightOneSpectrum.adicCompletion.valued_coe F v (2 : F)).trans hval
  have hres : (2 : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ≠ 0 := by
    have h : IsUnit (2 : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
      convert hunit.map (IsLocalRing.residue (v.adicCompletionIntegers F)) using 1 <;> simp only [map_ofNat]
    exact h.ne_zero
  intro he
  apply hres
  simpa only [he, Nat.cast_ofNat] using CharP.cast_eq_zero
    (IsLocalRing.ResidueField (v.adicCompletionIntegers F))
    (ringChar (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))

theorem conductor_shape_of_local_exponents (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (c f : Ideal (𝓞 F)) (hc : c ≠ ⊥) (hf : f ≠ ⊥)
    (hzero : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ Sf → idealPrimeExponent v.asIdeal c = 0)
    (hext : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf →
      idealPrimeExponent v.asIdeal f = idealPrimeExponent v.asIdeal c)
    (hbound : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ Sf →
      idealPrimeExponent v.asIdeal f ≤ idealPrimeExponent v.asIdeal c + squareUnitDepth v) :
    ∃ s : Ideal (𝓞 F), s ∣ uniformSquareUnitModulus Sf ∧ f = c * s := by
  have hdvd : c ∣ f := by
    rw [dvd_iff_normalizedFactors_le_normalizedFactors hc hf, Multiset.le_iff_count]
    intro p
    by_cases hp : p ∈ normalizedFactors c
    · obtain ⟨hpprime, hp0⟩ := (Ideal.mem_normalizedFactors_iff hc).mp hp
      let v : HeightOneSpectrum (𝓞 F) := ⟨p, hpprime, fun h => hc (le_bot_iff.mp (h ▸ hp0))⟩
      by_cases hv : v ∈ Sf
      · change idealPrimeExponent p c ≤ _
        rw [show idealPrimeExponent p c = 0 from hzero v hv]
        exact Nat.zero_le _
      · exact (hext v hv).ge
    · simp [Multiset.count_eq_zero.mpr hp]
  obtain ⟨s, hs⟩ := hdvd
  have hs0 : s ≠ ⊥ := right_ne_zero_of_mul (hs ▸ hf)
  refine ⟨s, ?_, hs⟩
  rw [dvd_iff_normalizedFactors_le_normalizedFactors hs0 (uniformSquareUnitModulus_spec Sf).1,
    Multiset.le_iff_count]
  intro p
  by_cases hp : p ∈ normalizedFactors s
  · obtain ⟨hpprime, hp0⟩ := (Ideal.mem_normalizedFactors_iff hs0).mp hp
    let v : HeightOneSpectrum (𝓞 F) := ⟨p, hpprime, fun h => hs0 (le_bot_iff.mp (h ▸ hp0))⟩
    have hexp : idealPrimeExponent p f = idealPrimeExponent p c + idealPrimeExponent p s := by
      simp [idealPrimeExponent, hs, normalizedFactors_mul hc hs0]
    by_cases hv : v ∈ Sf
    · have hpow : v.asIdeal ^ squareUnitDepth v ∣ uniformSquareUnitModulus Sf :=
        Finset.dvd_prod_of_mem _ hv
      have hle : idealPrimeExponent p s ≤ squareUnitDepth v := by
        have hb := hbound v hv
        change idealPrimeExponent p f ≤ idealPrimeExponent p c + squareUnitDepth v at hb
        omega
      have hpcount : (normalizedFactors (v.asIdeal ^ squareUnitDepth v)).count p = squareUnitDepth v := by
        simp [v.irreducible.normalizedFactors_pow, v]
      have hfac := (dvd_iff_normalizedFactors_le_normalizedFactors
        (pow_ne_zero _ v.ne_bot) (uniformSquareUnitModulus_spec Sf).1).mp hpow
      exact hle.trans (hpcount ▸ (Multiset.le_iff_count.mp hfac p))
    · have he := hext v hv
      change idealPrimeExponent p f = idealPrimeExponent p c at he
      change idealPrimeExponent p s ≤ _
      have hz : idealPrimeExponent p s = 0 := by omega
      simp [hz]
  · simp [Multiset.count_eq_zero.mpr hp]

theorem squarefree_conductor_shape_of_depth_bound (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (c : Ideal (𝓞 F)) (hc : Squarefree c)
    (hcop : c ⊔ uniformSquareUnitModulus A.Sf = ⊤)
    (hbound : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ A.Sf →
      idealPrimeExponent v.asIdeal (RMKummerConductor.m F h12
        (KummerSquarefreeMembers.generator A σ η hS C c hc hcop)) ≤ squareUnitDepth v) :
    ∃ s : Ideal (𝓞 F), s ∣ uniformSquareUnitModulus A.Sf ∧
      RMKummerConductor.m F h12
        (KummerSquarefreeMembers.generator A σ η hS C c hc hcop) = c * s := by
  let x := KummerSquarefreeMembers.generator A σ η hS C c hc hcop
  have hzero (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ A.Sf) :
      idealPrimeExponent v.asIdeal c = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hf
    have hc' := (Ideal.mem_normalizedFactors_iff hc.ne_zero).mp hf |>.2
    have hq := (uniformSquareUnitModulus_spec A.Sf).2.1 v |>.mpr hv
    exact v.isPrime.ne_top (top_le_iff.mp (hcop ▸ sup_le hc' hq))
  apply conductor_shape_of_local_exponents A.Sf c (RMKummerConductor.m F h12 x)
    hc.ne_zero (RMKummerConductor.m_ne_bot F h12 x) hzero
  · intro v hv
    have he := RMTameQuadraticExponent.conductor_exponent_eq_parity F h12 x v
      (residue_odd_outside A v hv)
    rw [generator_radicalOrder A σ η hS C c hc hcop v hv] at he
    have hn : idealPrimeExponent v.asIdeal c ≤ 1 :=
      Multiset.nodup_iff_count_le_one.mp
        ((squarefree_iff_nodup_normalizedFactors hc.ne_zero).mp hc) _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with hn | hn
    · rw [hn] at he ⊢
      simpa using he
    · rw [hn] at he ⊢
      simpa using he
  · intro v hv
    rw [hzero v hv, zero_add]
    exact hbound v hv

theorem higher_unit_one_add_four (v : HeightOneSpectrum (𝓞 F))
    (t : (v.adicCompletion F)ˣ)
    (ht : t ∈ ClassFieldTheory.rayLocalHigherUnitGroup v (squareUnitDepth v)) :
    ∃ b : v.adicCompletionIntegers F, b ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ∧
      (t : v.adicCompletion F) = ((1 + 4 * b : v.adicCompletionIntegers F) : v.adicCompletion F) := by
  let O := v.adicCompletionIntegers F
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, htwo⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (x := (2 : O)) (by norm_num) hϖ
  have hn : squareUnitDepth v = 2 * n + 1 := by
    dsimp [squareUnitDepth, squareUnitOrdTwo]
    rw [IsDiscreteValuationRing.addVal_def (2 : O) u hϖ n htwo]
    simp
  have hfour : (4 : O) = (u * u : Oˣ) * ϖ ^ (2 * n) := by
    calc (4 : O) = (2 : O) * 2 := by norm_num
         _ = (u * u : Oˣ) * ϖ ^ (2 * n) := by rw [htwo]; simp [pow_mul]; ring
  have hspan : Ideal.span {(4 : O)} = IsLocalRing.maximalIdeal O ^ (2 * n) := by
    rw [hfour, Ideal.span_singleton_mul_left_unit (u * u).isUnit,
      hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  obtain ⟨a, ha, htval⟩ := (ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff_exists_one_add
    v (squareUnitDepth v) (squareUnitDepth_bounds v).1 t).mp ht
  have ha' : a ∈ Ideal.span {(4 : O)} * IsLocalRing.maximalIdeal O := by
    rw [hspan, ← pow_succ, ← hn]
    exact ha
  obtain ⟨b, hb, hab⟩ := Ideal.mem_span_singleton_mul.mp ha'
  refine ⟨b, hb, ?_⟩
  rw [htval, hab]

theorem conductor_depth_of_higher_unit_squares
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (hsq : ∀ t : (v.adicCompletion F)ˣ,
      t ∈ ClassFieldTheory.rayLocalHigherUnitGroup v (squareUnitDepth v) →
      IsSquare (t : v.adicCompletion F)) :
    idealPrimeExponent v.asIdeal (RMKummerConductor.m F h12 x) ≤ squareUnitDepth v := by
  apply (RMKummerCharacterAPI.local_conductor F h12 x v).2
  intro t ht
  apply MonoidHom.mem_ker.mpr
  obtain ⟨y, hy⟩ := hsq t ht
  let K := v.adicCompletion F
  letI : ValuativeRel K := ClassFieldTheory.finitePlaceCompletionValuativeRel F v
  letI : IsNonarchimedeanLocalField K :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v
  have hy0 : y ≠ 0 := by
    intro h
    apply t.ne_zero
    rw [hy, h, mul_zero]
  let c : Kˣ := Units.mk0 y hy0
  have ht' : t = c * c := by
    apply Units.ext
    exact hy
  have h2 := RMKummerLocalHilbertComparison.localTwo_ne_zero F v
  have hmu := RMKummerLocalHilbertComparison.localPrimitiveTwo F h12 v
  have hsym : ClassFieldTheory.localHilbertSymbol K (2 : ℕ+) h2 hmu t
      (Units.map (algebraMap F K).toMonoidHom x) = 1 := by
    rw [ht']
    erw [ClassFieldTheory.localHilbertSymbol_mul_left]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
    exact (ClassFieldTheory.localHilbertSymbol K (2 : ℕ+) h2 hmu c
      (Units.map (algebraMap F K).toMonoidHom x)).property
  rw [RMKummerLocalHilbertComparison.lambda_eq_inverse_localHilbertSymbol F h12 x v t,
    hsym]
  erw [map_one]
  exact inv_one
private theorem squareOneAddFour {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianRing R (IsLocalRing.maximalIdeal R)]
    (b : R) (hb : b ∈ IsLocalRing.maximalIdeal R) : IsSquare (1 + 4*b) := by
  let f : Polynomial R := Polynomial.X ^ 2 + Polynomial.X - Polynomial.C b
  have hf : f.Monic := by
    apply Polynomial.Monic.sub_of_left
    · exact Polynomial.Monic.add_of_left (Polynomial.monic_X_pow 2) (by simp)
    · have hd : (Polynomial.X ^ 2 + Polynomial.X : Polynomial R).degree = 2 := by
        rw [Polynomial.degree_add_eq_left_of_degree_lt] <;> simp
      rw [hd]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
  obtain ⟨y, hy, -⟩ := HenselianRing.is_henselian
    (I := IsLocalRing.maximalIdeal R) f hf 0
    (by simpa [f] using (IsLocalRing.maximalIdeal R).neg_mem hb)
    (by simp [f])
  have hy' : y*y + y - b = 0 := by simpa [f, Polynomial.IsRoot, pow_two] using hy
  refine ⟨1 + 2*y, ?_⟩
  linear_combination -4 * hy'

theorem squareUnitDepth_higher_units_are_squares (v : HeightOneSpectrum (𝓞 F))
    (t : (v.adicCompletion F)ˣ)
    (ht : t ∈ ClassFieldTheory.rayLocalHigherUnitGroup v (squareUnitDepth v)) :
    IsSquare (t : v.adicCompletion F) := by
  let R := v.adicCompletionIntegers F
  letI : HenselianRing R (IsLocalRing.maximalIdeal R) :=
    ValuationTheory.DiscreteValuationField.Valuation.henselianRing
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
  obtain ⟨b, hb, ht'⟩ := higher_unit_one_add_four v t ht
  obtain ⟨y, hy⟩ := squareOneAddFour b hb
  refine ⟨(y : v.adicCompletion F), ?_⟩
  rw [ht']
  exact congrArg (fun x : R => (x : v.adicCompletion F)) hy

theorem squarefree_conductor_shape (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (c : Ideal (𝓞 F)) (hc : Squarefree c)
    (hcop : c ⊔ uniformSquareUnitModulus A.Sf = ⊤) :
    ∃ s : Ideal (𝓞 F), s ∣ uniformSquareUnitModulus A.Sf ∧
      RMKummerConductor.m F h12
        (KummerSquarefreeMembers.generator A σ η hS C c hc hcop) = c * s := by
  apply squarefree_conductor_shape_of_depth_bound h12 A σ η hS C c hc hcop
  intro v _
  exact conductor_depth_of_higher_unit_squares h12 _ v
    (squareUnitDepth_higher_units_are_squares v)

end
end DedekindZetaZeroFree.RMKummerConductorArithmetic

end

section

namespace DedekindZetaZeroFree.RMKummerConductorArithmetic
noncomputable section
open scoped NumberField Classical
open IsDedekindDomain UniqueFactorizationMonoid
variable {F : Type} [Field F] [NumberField F]

private theorem exp_mul (a b : Ideal (𝓞 F)) (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 F)) :
    idealPrimeExponent v.asIdeal (a * b) = idealPrimeExponent v.asIdeal a + idealPrimeExponent v.asIdeal b := by
  simp [idealPrimeExponent, normalizedFactors_mul ha hb]
private theorem exp_le_one (a : Ideal (𝓞 F)) (ha : Squarefree a)
    (v : HeightOneSpectrum (𝓞 F)) : idealPrimeExponent v.asIdeal a ≤ 1 := by
  exact Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors ha.ne_zero).mp ha) _
private theorem exp_zero (a : Ideal (𝓞 F)) (ha : a ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ a ≤ v.asIdeal) : idealPrimeExponent v.asIdeal a = 0 := by
  apply Multiset.count_eq_zero.mpr
  intro h
  exact hv ((Ideal.mem_normalizedFactors_iff ha).mp h).2
private theorem coprime_exp (a b : Ideal (𝓞 F)) (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (hab : a ⊔ b = ⊤) (v : HeightOneSpectrum (𝓞 F)) :
    idealPrimeExponent v.asIdeal a = 0 ∨ idealPrimeExponent v.asIdeal b = 0 := by
  by_contra h
  push Not at h
  have hi : a ≤ v.asIdeal := ((Ideal.mem_normalizedFactors_iff ha).mp
    (Multiset.count_pos.mp (Nat.pos_of_ne_zero h.1))).2
  have hj : b ≤ v.asIdeal := ((Ideal.mem_normalizedFactors_iff hb).mp
    (Multiset.count_pos.mp (Nat.pos_of_ne_zero h.2))).2
  exact v.isPrime.ne_top (top_unique (hab ▸ sup_le hi hj))
private theorem odd_residue (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    ringChar (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ≠ 2 := by
  have htwo : (2 : 𝓞 F) ∉ v.asIdeal := by
    intro h
    apply hv
    apply A.above_six v
    have h6 := v.asIdeal.mul_mem_right (3 : 𝓞 F) h
    norm_num at h6 ⊢
    exact h6
  let e : (𝓞 F ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (finitePlaceIdealResidueEquivCompletion v).trans
      (IsLocalRing.ResidueField.mapEquiv (finitePlaceCompletionIntegerRingEquiv v))
  intro hc
  have hz : (2 : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = 0 := by
    haveI : CharP (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) 2 := ringChar.of_eq hc
    exact CharP.cast_eq_zero _ 2
  have hq : (2 : 𝓞 F ⧸ v.asIdeal) = 0 := e.injective (by simpa only [map_ofNat, map_zero] using hz)
  exact htwo ((Ideal.Quotient.eq_zero_iff_mem).mp hq)

theorem equal_class_quotient_conductor (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (a b : Ideal (𝓞 F)) (ha : Squarefree a)
    (hqa : a ⊔ uniformSquareUnitModulus A.Sf = ⊤)
    (hb : Squarefree b) (hqb : b ⊔ uniformSquareUnitModulus A.Sf = ⊤)
    (hab : a ⊔ b = ⊤) (hcls : C.integralCls a = C.integralCls b) :
    RMKummerConductor.m F h12
      (KummerProductPrimitive.quotientRadical A σ η hS C a b ha hb hqa hqb) = a * b := by
  let ia := KummerSquarefreeMembers.exteriorIndex A a ha hqa
  let ib := KummerSquarefreeMembers.exteriorIndex A b hb hqb
  let ra := KummerSquarefreeMembers.chooseRepresentative A σ η hS C ia
  let rb := KummerSquarefreeMembers.chooseRepresentative A σ η hS C ib
  let x := KummerProductPrimitive.quotientRadical A σ η hS C a b ha hb hqa hqb
  have hx : x = ra.radical / rb.radical := rfl
  have hca : (C.cls (A.exteriorFractional ia)).val = A.finiteSquareClass (A.diagonal ra.radical) := by
    apply C.cls_allowed_generator
    rw [SArithmeticData.exteriorFractional_val]
    exact ra.isAllowedGenerator
  have hcb : (C.cls (A.exteriorFractional ib)).val = A.finiteSquareClass (A.diagonal rb.radical) := by
    apply C.cls_allowed_generator
    rw [SArithmeticData.exteriorFractional_val]
    exact rb.isAllowedGenerator
  have hcc : C.cls (A.exteriorFractional ia) = C.cls (A.exteriorFractional ib) := by
    rw [← C.integralCls_exterior ia, ← C.integralCls_exterior ib]
    exact hcls
  have hsquare : ∀ v : {v // v ∈ A.Sf}, IsSquare (algebraMap F (v.val.adicCompletion F) (x : F)) := by
    intro v
    have hc := congrFun (hca.symm.trans ((congrArg Subtype.val hcc).trans hcb)) v
    change ClassFieldTheory.powerClass _ 2 ((A.diagonal ra.radical).2 v) =
      ClassFieldTheory.powerClass _ 2 ((A.diagonal rb.radical).2 v) at hc
    obtain ⟨y, hy⟩ := (ClassFieldTheory.powerClass_eq_iff _ 2 _ _).mp hc
    refine ⟨(y : v.val.adicCompletion F), ?_⟩
    have hy' := congrArg Units.val hy
    simpa [hx, pow_two, SArithmeticData.diagonal] using hy'.symm
  have hord : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      RMTameQuadraticExponent.radicalOrder F v x =
      (idealPrimeExponent v.asIdeal a : ℤ) - (idealPrimeExponent v.asIdeal b : ℤ) := by
    intro v hv
    have hva := ArithmeticContext.actual_generator_valuation A ia ra.integral ra.generates ra.radical ra.radical_eq v hv
    have hvb := ArithmeticContext.actual_generator_valuation A ib rb.integral rb.generates rb.radical rb.radical_eq v hv
    simp only [ia, ib, KummerSquarefreeMembers.exteriorIndex_val] at hva hvb
    rw [RMTameQuadraticExponent.radicalOrder, hx, Units.val_div_eq_div_val, map_div₀, hva, hvb,
      ← WithZero.exp_sub, WithZero.log_exp]
    ring
  have he : ∀ v : HeightOneSpectrum (𝓞 F), idealPrimeExponent v.asIdeal (RMKummerConductor.m F h12 x) = idealPrimeExponent v.asIdeal (a * b) := by
    intro v
    by_cases hv : v ∈ A.Sf
    · have htriv : ClassFieldTheory.rayLocalHigherUnitGroup v 0 ≤ (RMKummerCharacterAPI.lambda F h12 x v).ker := by
        intro t ht
        exact MonoidHom.mem_ker.mpr (RMTameQuadraticExponent.lambda_eq_one_of_local_square F h12 x v (hsquare ⟨v, hv⟩) t)
      have hzero := (RMKummerCharacterAPI.local_conductor F h12 x v).2 htriv
      have hna : ¬ a ≤ v.asIdeal := by
        intro h
        have hs : A.cS ≤ v.asIdeal := by
          exact (Ideal.prod_le_inf : (∏ w ∈ A.Sf, w.asIdeal) ≤ A.Sf.inf (fun w => w.asIdeal)).trans (Finset.inf_le hv)
        exact v.isPrime.ne_top (top_unique ((KummerSquarefreeMembers.exterior_iff A a).mp hqa ▸ sup_le h hs))
      have hnb : ¬ b ≤ v.asIdeal := by
        intro h
        have hs : A.cS ≤ v.asIdeal := by
          exact (Ideal.prod_le_inf : (∏ w ∈ A.Sf, w.asIdeal) ≤ A.Sf.inf (fun w => w.asIdeal)).trans (Finset.inf_le hv)
        exact v.isPrime.ne_top (top_unique ((KummerSquarefreeMembers.exterior_iff A b).mp hqb ▸ sup_le h hs))
      rw [exp_mul a b ha.ne_zero hb.ne_zero v, exp_zero a ha.ne_zero v hna, exp_zero b hb.ne_zero v hnb]
      exact Nat.eq_zero_of_le_zero hzero
    · rw [RMTameQuadraticExponent.conductor_exponent_eq_parity F h12 x v (odd_residue A v hv), hord v hv, exp_mul a b ha.ne_zero hb.ne_zero v]
      have hla := exp_le_one a ha v
      have hlb := exp_le_one b hb v
      have hc := coprime_exp a b ha.ne_zero hb.ne_zero hab v
      rcases hc with hc | hc <;> rw [hc] <;>
        interval_cases h : idealPrimeExponent v.asIdeal a <;>
        interval_cases h' : idealPrimeExponent v.asIdeal b <;> norm_num
  rw [← Ideal.iInf_maxPowDividing_eq (RMKummerConductor.m_ne_bot F h12 x),
    ← Ideal.iInf_maxPowDividing_eq (mul_ne_zero ha.ne_zero hb.ne_zero)]
  apply iInf_congr
  intro v
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count v (RMKummerConductor.m_ne_bot F h12 x),
    HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count v (mul_ne_zero ha.ne_zero hb.ne_zero)]
  exact congrArg (fun n => v.asIdeal ^ n) (he v)

end
end DedekindZetaZeroFree.RMKummerConductorArithmetic

end

section

namespace DedekindZetaZeroFree.RMKummerConductorArithmetic
noncomputable section
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]

open IsDedekindDomain
open ClassFieldTheory
set_option backward.isDefEq.respectTransparency false

private theorem quadratic_value_ext {K : Type*} [Field K] (a b : K)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (h : a = 1 ↔ b = 1) : a = b := by
  rcases sq_eq_one_iff.mp ha with ha | ha
  · exact ha.trans (h.mp ha).symm
  · rcases sq_eq_one_iff.mp hb with hb | hb
    · exact (h.mpr hb).trans hb.symm
    · exact ha.trans hb.symm

theorem lambda_diagonal_eq_actual_two (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ) (x a : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (RMKummerLocalNormCharacter.lambda F h12 x v
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) : ℂ) =
      σ ((A.actualLocalSymbol v 2 (Or.inl rfl)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x)).val : F) := by
  letI : ValuativeRel (v.adicCompletion F) := finitePlaceCompletionValuativeRel F v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    finitePlaceCompletionIsNonarchimedeanLocalField F v
  let au := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a
  let xu := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x
  let z := A.actualLocalSymbol v 2 (Or.inl rfl) au xu
  let H := localHilbertSymbol (v.adicCompletion F) 2
    (RMKummerLocalHilbertComparison.localTwo_ne_zero F v)
    (RMKummerLocalHilbertComparison.localPrimitiveTwo F h12 v) au xu
  have hz : (z.val : F) ^ 2 = 1 := congrArg Units.val z.property
  apply quadratic_value_ext
  · exact congrArg Units.val (RMKummerLocalNormCharacter.lambda_pow_two F h12 x v au)
  · simpa only [← map_pow, ← map_one σ] using congrArg σ hz
  · have hσ : σ (z.val : F) = 1 ↔ z = 1 := by
      rw [← map_one σ, σ.injective.eq_iff]
      exact ⟨fun h => Subtype.ext (Units.ext h), fun h => by rw [h]; rfl⟩
    have hlambda : (RMKummerLocalNormCharacter.lambda F h12 x v au : ℂ) = 1 ↔ H = 1 := by
      have hh := RMKummerLocalHilbertComparison.lambda_eq_inverse_localHilbertSymbol
        F h12 x v au
      rw [← Units.val_one, Units.val_inj, hh, inv_eq_one,
        ← map_one (rmKummerQuadraticRootsComplexMap F h12 (v.adicCompletion F))]
      erw [(rmKummerQuadraticRootsComplexMap_injective F h12 (v.adicCompletion F)).eq_iff]
    have hzH : z = 1 ↔ H = 1 := by
      have he := (A.finiteRootsEquiv v 2 (Or.inl rfl)).injective.eq_iff (a := z) (b := 1)
      rw [(A.finiteRootsEquiv v 2 (Or.inl rfl)).map_one] at he
      apply he.symm.trans
      change A.finiteRootsEquiv v 2 (Or.inl rfl)
        (A.actualLocalHilbert v 2 (Or.inl rfl) (powerClass _ 2 au) (powerClass _ 2 xu)) = 1 ↔ H = 1
      have hlocal := A.actualLocalHilbert_local_value v (2 : ℕ+) (Or.inl rfl)
        (powerClass _ 2 au) (powerClass _ 2 xu)
      apply (show _ ↔ _ from Iff.of_eq (congrArg (fun q => q = 1) hlocal)).trans
      rw [inv_eq_one]
      exact ((A.actualRawHilbert_isLocal 2 (Or.inl rfl) v).2.2.2 au xu).trans
        (localHilbertSymbol_eq_one_iff_isKummerNorm _ 2 _ _ au xu).symm
    exact hlambda.trans (hzH.symm.trans hσ.symm)

theorem lambda_diagonal_eq_actual_six_cube (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ) (x a : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (RMKummerLocalNormCharacter.lambda F h12 x v
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) : ℂ) =
      σ ((A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl))
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x)).val : F) ^ 3 := by
  rw [lambda_diagonal_eq_actual_two h12 A σ]
  rw [← map_pow σ]
  apply congrArg σ
  apply (algebraMap F (v.adicCompletion F)).injective
  have hh := congrArg Units.val (A.actualLocalSymbol_two_six v
    (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
    (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x))
  simpa only [Units.val_pow_eq_pow_val, A.finiteRootsEquiv_apply, map_pow] using hh

theorem lambda_uniformizer_eq_cubic_residue (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hI : I.val = v.asIdeal)
    (hc : (Ideal.absNorm v.asIdeal).Coprime 6)
    (hv : v ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces F 6)
    (hvS : v ∉ A.Sf) (b : A.R) (x : Fˣ) (hx : (x : F) = (b : F))
    (hval : v.valuation F (x : F) = 1) (a : Fˣ)
    (ha : v.valuation F (a : F) = WithZero.exp (-1 : ℤ)) :
    (RMKummerLocalNormCharacter.lambda F h12 x v
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) : ℂ) =
      σ (A.sexticResidue I b) ^ 3 := by
  rw [lambda_diagonal_eq_actual_six_cube h12 A σ]
  have ht := ArithmeticContext.actual_sextic_local_sinteger_tame A I v hI
    hc hv hvS b x hx hval a
  have he : -GlobalClassFieldTheory.Reciprocity.finitePlaceNormalizedValuation F v a = 1 := by
    rw [ArithmeticContext.actual_cft_normalizedValuation_log, ha, WithZero.log_exp]
    rfl
  rw [he, zpow_one] at ht
  rw [ht]

theorem Xi_prime_eq_lambda_global_uniformizer (h12 : (primitiveRoots 12 F).Nonempty)
    (x a : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (M F (RMKummerConductor.m F h12 x)
      (RMKummerConductor.m_ne_bot F h12 x)).finitePart.support)
    (ha : v.valuation F (a : F) = WithZero.exp (-1 : ℤ)) :
    RMKummerConductor.Xi F h12 x v.asIdeal =
      (RMKummerLocalNormCharacter.lambda F h12 x v
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) : ℂ) := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 (RMKummerConductor.E F h12 x)) v.asIdeal
  letI : P.IsMaximal := hP
  letI : P.LiesOver v.asIdeal := hPv
  have hP0 : P ≠ ⊥ := by
    intro he
    apply v.ne_bot
    have hcom := (Ideal.over_def P v.asIdeal)
    rw [he] at hcom
    simpa using hcom
  let w : HeightOneSpectrum (𝓞 (RMKummerConductor.E F h12 x)) :=
    ⟨P, hP.isPrime, hP0⟩
  rw [RMKummerPrincipalPrime.prime_arithmeticFrobenius F h12 x v hv w hPv]
  apply congrArg Units.val
  apply RMKummerPrincipalPrime.arithmeticFrobenius_eq_lambda_uniformizer F h12 x v hv w hPv
  exact (HeightOneSpectrum.adicCompletion.valued_coe F v (a : F)).trans ha

theorem actual_cubic_sextic_prime_disjoint (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (c : Ideal (𝓞 F)) (hc : Squarefree c)
    (hcopc : c ⊔ uniformSquareUnitModulus A.Sf = ⊤)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hI : I.val = v.asIdeal)
    (hdisj : c ⊔ v.asIdeal = ⊤) :
    RMKummerConductor.Xi F h12
      (KummerSquarefreeMembers.generator A σ η hS C c hc hcopc) v.asIdeal =
      KummerExteriorValues.cubicSexticValue A σ η hS C
        (KummerSquarefreeMembers.exteriorIndex A c hc hcopc) I := by
  let rep := KummerSquarefreeMembers.chooseRepresentative A σ η hS C
    (KummerSquarefreeMembers.exteriorIndex A c hc hcopc)
  let x := KummerSquarefreeMembers.generator A σ η hS C c hc hcopc
  have hvS := ArithmeticContext.actual_exterior_prime_outside A I v hI
  obtain ⟨s, hs, hshape⟩ := squarefree_conductor_shape h12 A σ η hS C c hc hcopc
  have hscop : v.asIdeal ⊔ s = ⊤ := by
    have hh : v.asIdeal ⊔ uniformSquareUnitModulus A.Sf = ⊤ :=
      (KummerSquarefreeMembers.exterior_iff A v.asIdeal).mpr (hI ▸ I.property.2)
    apply top_unique
    rw [← hh]
    exact sup_le_sup_left (Ideal.dvd_iff_le.mp hs) _
  have hcop : v.asIdeal ⊔ RMKummerConductor.m F h12 x = ⊤ := by
    rw [hshape, Ideal.sup_mul_eq_of_coprime_left (sup_comm c v.asIdeal ▸ hdisj), hscop]
  have hgood : v ∉ (M F (RMKummerConductor.m F h12 x)
      (RMKummerConductor.m_ne_bot F h12 x)).finitePart.support := by
    rw [Finsupp.notMem_support_iff, M_finitePart, idealPrimeExponent, Multiset.count_eq_zero]
    intro hf
    have hle := (Ideal.mem_normalizedFactors_iff (RMKummerConductor.m_ne_bot F h12 x)).mp hf |>.2
    exact v.isPrime.ne_top (top_le_iff.mp (hcop ▸ sup_le le_rfl hle))
  obtain ⟨a, ha⟩ := v.valuation_exists_uniformizer F
  have ha0 : a ≠ 0 := by
    intro hz
    rw [hz, map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  let au := Units.mk0 a ha0
  rw [Xi_prime_eq_lambda_global_uniformizer h12 x au v hgood ha]
  apply lambda_uniformizer_eq_cubic_residue h12 A σ I v hI
    (ArithmeticContext.actual_outside_norm_coprime_six A v hvS)
    (ArithmeticContext.actual_outside_exponent_support A v hvS) hvS
    rep.integral x rep.radical_eq _ au ha
  have he : idealPrimeExponent v.asIdeal c = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hf
    have hle := (Ideal.mem_normalizedFactors_iff hc.ne_zero).mp hf |>.2
    exact v.isPrime.ne_top (top_le_iff.mp (hdisj ▸ sup_le hle le_rfl))
  have hh := SIntegerLocalization.generator_valuation A.Sf c hc.ne_zero
    rep.integral rep.generates.1 rep.generates.2 v hvS
  rw [he, Nat.cast_zero, neg_zero, WithZero.exp_zero] at hh
  exact rep.radical_eq ▸ hh

theorem actual_cubic_sextic_prime (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (c : Ideal (𝓞 F)) (hc : Squarefree c)
    (hcopc : c ⊔ uniformSquareUnitModulus A.Sf = ⊤)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hI : I.val = v.asIdeal) :
    RMKummerConductor.Xi F h12
      (KummerSquarefreeMembers.generator A σ η hS C c hc hcopc) v.asIdeal =
      KummerExteriorValues.cubicSexticValue A σ η hS C
        (KummerSquarefreeMembers.exteriorIndex A c hc hcopc) I := by
  by_cases hh : c ⊔ v.asIdeal = ⊤
  · exact actual_cubic_sextic_prime_disjoint h12 A σ η hS C c hc hcopc I v hI hh
  · have hzero := KummerExteriorValues.cubicSexticValue_shared_zero A σ η hS C
      (KummerSquarefreeMembers.exteriorIndex A c hc hcopc) I (hI ▸ hh)
    rw [hzero.1]
    apply ((RMKummerConductor.Xi F h12 _).eq_zero_iff' v.asIdeal).mpr
    right
    obtain ⟨s, hs, hshape⟩ := squarefree_conductor_shape h12 A σ η hS C c hc hcopc
    rw [hshape]
    intro he
    apply hh
    apply top_unique
    rw [← he]
    exact sup_le le_sup_right (Ideal.mul_le_left.trans le_sup_left)

theorem actual_cubic_sextic_value (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (c : Ideal (𝓞 F)) (hc : Squarefree c)
    (hcopc : c ⊔ uniformSquareUnitModulus A.Sf = ⊤)
    (d : Ideal (𝓞 F)) (hd : d ≠ ⊥)
    (hcopd : d ⊔ uniformSquareUnitModulus A.Sf = ⊤) :
    RMKummerConductor.Xi F h12
      (KummerSquarefreeMembers.generator A σ η hS C c hc hcopc) d =
      KummerExteriorValues.cubicSexticValue A σ η hS C
        (KummerSquarefreeMembers.exteriorIndex A c hc hcopc)
        (KummerExteriorValues.exteriorIndex A d hd hcopd) := by
  let x := KummerSquarefreeMembers.generator A σ η hS C c hc hcopc
  let rep := KummerSquarefreeMembers.chooseRepresentative A σ η hS C
    (KummerSquarefreeMembers.exteriorIndex A c hc hcopc)
  have hall : ∀ (e : Ideal (𝓞 F)) (J : A.Exterior), J.val = e →
      RMKummerConductor.Xi F h12 x e = σ (A.sexticResidue J rep.integral) ^ 3 := by
    intro e
    induction e using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro J hJ
      exact (J.property.1 hJ).elim
    | h₂ e he =>
      intro J hJ
      have ht : J.val = ⊤ := hJ.trans (Ideal.isUnit_iff.mp he)
      rw [Ideal.isUnit_iff.mp he, (RMKummerConductor.Xi F h12 x).map_top',
        ArithmeticContext.actual_sextic_top A J ht, map_one, one_pow]
    | h₃ e p he hp ih =>
      intro J hJ
      have heS : e ⊔ A.cS = ⊤ := by
        apply top_unique
        rw [← J.property.2, hJ]
        exact sup_le_sup_right Ideal.mul_le_right _
      have hpS : p ⊔ A.cS = ⊤ := by
        apply top_unique
        rw [← J.property.2, hJ]
        exact sup_le_sup_right Ideal.mul_le_left _
      let Ie : A.Exterior := ⟨e, he, heS⟩
      let Ip : A.Exterior := ⟨p, hp.ne_zero, hpS⟩
      have hmul := A.sexticResidueFamily_normalized.2.2 Ip Ie J hJ rep.integral
      change A.sexticResidue J rep.integral =
        A.sexticResidue Ip rep.integral * A.sexticResidue Ie rep.integral at hmul
      have hprime := actual_cubic_sextic_prime h12 A σ η hS C c hc hcopc Ip
        (HeightOneSpectrum.ofPrime hp) rfl
      change RMKummerConductor.Xi F h12 x p = σ (A.sexticResidue Ip rep.integral) ^ 3 at hprime
      rw [(RMKummerConductor.Xi F h12 x).map_mul', ih Ie rfl, hprime,
        hmul, map_mul, mul_pow]
  exact hall d (KummerExteriorValues.exteriorIndex A d hd hcopd) rfl

end
end DedekindZetaZeroFree.RMKummerConductorArithmetic

end

section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

namespace RMKummerFamily
variable {F : Type} [Field F] [NumberField F]

def ExactOutput (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (ℱ : QuadraticHeckeFamily F (uniformSquareUnitModulus A.Sf)) : Prop :=
  ℱ.cond = KummerFamilyAssembly.totalConductor A σ η hS C
      (RMKummerConductor.m F h12) ∧
  (∀ c n : Ideal (𝓞 F), ℱ.χ c n =
    KummerFamilyAssembly.totalCharacter A σ η hS C
      (RMKummerConductor.m F h12) (RMKummerConductor.Xi F h12) c n) ∧
  ℱ.G = (A.B₂ C.correction.B) ∧
  HEq ℱ.instGroup (inferInstance : Group (A.B₂ C.correction.B)) ∧
  (∀ c : Ideal (𝓞 F), HEq (ℱ.cls c) (C.integralCls c)) ∧
  (∀ g h : ℱ.G, ℱ.C g h = 1) ∧
  (∀ (c : Ideal (𝓞 F)) (hc : Squarefree c)
      (hcop : c ⊔ uniformSquareUnitModulus A.Sf = ⊤),
    ∃ s : Ideal (𝓞 F), s ∣ uniformSquareUnitModulus A.Sf ∧
      ℱ.cond c = c * s) ∧
  (∀ (c : Ideal (𝓞 F)) (hc : Squarefree c)
      (hcopc : c ⊔ uniformSquareUnitModulus A.Sf = ⊤)
      (d : Ideal (𝓞 F)) (hd : d ≠ ⊥)
      (hcopd : d ⊔ uniformSquareUnitModulus A.Sf = ⊤),
    ℱ.χ c d = KummerExteriorValues.cubicSexticValue A σ η hS C
      (KummerSquarefreeMembers.exteriorIndex A c hc hcopc)
      (KummerExteriorValues.exteriorIndex A d hd hcopd)) ∧
  (∀ (c : Ideal (𝓞 F)) (hc : Squarefree c)
      (hcopc : c ⊔ uniformSquareUnitModulus A.Sf = ⊤)
      (d : Ideal (𝓞 F)) (hd : d ≠ ⊥)
      (hcopd : d ⊔ uniformSquareUnitModulus A.Sf = ⊤),
    c ⊔ d ≠ ⊤ → ℱ.χ c d = 0) ∧
  KummerProductPrimitive.ExactProductOutput A σ η hS C
    (RMKummerConductor.m F h12) (RMKummerConductor.Xi F h12) ∧
  ℱ.cond ⊤ = ⊤ ∧
  (∀ n : Ideal (𝓞 F), ℱ.χ ⊤ n = KummerFamilyAssembly.trivialTop n) ∧
  (∀ c : Ideal (𝓞 F), ¬ KummerFamilyAssembly.Constrained A c →
    ℱ.cond c = ⊤ ∧
      ∀ n : Ideal (𝓞 F), ℱ.χ c n = KummerFamilyAssembly.trivialTop n)

theorem totalConductor_top (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS) :
    KummerFamilyAssembly.totalConductor A σ η hS C (RMKummerConductor.m F h12) ⊤ = ⊤ := by
  have hc : KummerFamilyAssembly.Constrained A ⊤ := ⟨by simpa only [Ideal.one_eq_top] using (squarefree_one : Squarefree (1 : Ideal (𝓞 F))), top_sup_eq _⟩
  rw [KummerFamilyAssembly.totalConductor_constrained _ _ _ _ _ _ _ hc]
  obtain ⟨y, hy⟩ := KummerSquarefreeMembers.representative_top_square
    (KummerSquarefreeMembers.chooseRepresentative A σ η hS C
      (KummerSquarefreeMembers.exteriorIndex A ⊤ hc.1 hc.2)) rfl
  change RMKummerConductor.m F h12
    (KummerSquarefreeMembers.chooseRepresentative A σ η hS C
      (KummerSquarefreeMembers.exteriorIndex A ⊤ hc.1 hc.2)).radical = ⊤
  rw [hy, ← one_mul (y ^ 2), RMKummerSquareConductor.m_mul_sq,
    RMKummerSquareConductor.m_one]

theorem totalCharacter_top_apply (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS) (n : Ideal (𝓞 F)) :
    KummerFamilyAssembly.totalCharacter A σ η hS C
      (RMKummerConductor.m F h12) (RMKummerConductor.Xi F h12) ⊤ n =
        KummerFamilyAssembly.trivialTop n := by
  have hc : KummerFamilyAssembly.Constrained A ⊤ := ⟨by simpa only [Ideal.one_eq_top] using (squarefree_one : Squarefree (1 : Ideal (𝓞 F))), top_sup_eq _⟩
  rw [KummerFamilyAssembly.totalCharacter_constrained_apply _ _ _ _ _ _ _ _ hc]
  obtain ⟨y, hy⟩ := KummerSquarefreeMembers.representative_top_square
    (KummerSquarefreeMembers.chooseRepresentative A σ η hS C
      (KummerSquarefreeMembers.exteriorIndex A ⊤ hc.1 hc.2)) rfl
  change RMKummerConductor.Xi F h12
    (KummerSquarefreeMembers.chooseRepresentative A σ η hS C
      (KummerSquarefreeMembers.exteriorIndex A ⊤ hc.1 hc.2)).radical n = _
  rw [hy, ← one_mul (y ^ 2), RMKummerSquareCharacter.Xi_mul_sq,
    RMKummerSquareCharacter.Xi_one]
  rfl

private theorem crtHigherUnits_iff (v : HeightOneSpectrum (𝓞 F)) (k : ℕ)
    (u : (v.adicCompletion F)ˣ) :
    CRTLocalHigherUnits F v k u ↔ u ∈ ClassFieldTheory.rayLocalHigherUnitGroup v k := by
  rw [ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff]
  rfl

private theorem crtSupport_eq (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    CRTIdealSupport F m = (M F m hm).finitePart.support := by
  ext v
  simp only [CRTIdealSupport, Finset.mem_preimage, Finsupp.mem_support_iff,
    M_finitePart, idealPrimeExponent, idealPrimeSupport, Multiset.mem_toFinset,
    ne_eq, Multiset.count_eq_zero, not_not]

theorem actualCharacter_primitive (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) :
    (RMKummerConductor.Xi F h12 x).IsPrimitive := by
  apply primitive_of_exact_local_exponents F
    (RMKummerConductor.totallyComplex F h12)
    (RMKummerConductor.m F h12 x) (RMKummerConductor.m_ne_bot F h12 x)
    (RMKummerConductor.Xi F h12 x)
    (fun v => RMKummerCharacterAPI.lambda F h12 x v.val)
  · intro v
    exact (RMKummerCharacterAPI.local_character F h12 x v.val).1
  · intro v u hu
    exact RMKummerCharacterAPI.local_trivial_on_conductor F h12 x v.val u
      ((crtHigherUnits_iff v.val _ u).mp hu)
  · intro v k hk
    obtain ⟨u, hu, hn⟩ := RMKummerLeastLocalExponent.lambda_nontrivial_below_conductor
      F h12 x v.val k hk
    exact ⟨u, (crtHigherUnits_iff v.val k u).mpr hu, hn⟩
  · intro α hα hcop
    rw [RMKummerPrincipalPrime.principal_product F h12 x α hα hcop]
    rw [← crtSupport_eq]
    simp only [← Finset.prod_inv_distrib, ← Units.val_inv_eq_inv_val, ← Units.coe_prod]
    congr 1
    change (∏ i ∈ CRTIdealSupport F (RMKummerConductor.m F h12 x),
      (RMKummerCharacterAPI.lambda F h12 x i (CRTIntegralLocalUnit F i α hα))⁻¹) = _
    exact (Finset.prod_coe_sort _ _).symm

open UniqueFactorizationMonoid

theorem quotient_unramified (h12 : (primitiveRoots 12 F).Nonempty) (x y : Fˣ)
    (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ v.asIdeal ∣ RMKummerConductor.m F h12 x * RMKummerConductor.m F h12 y) :
    ¬ v.asIdeal ∣ RMKummerConductor.m F h12 (x / y) := by
  have hx : idealPrimeExponent v.asIdeal (RMKummerConductor.m F h12 x) = 0 := by
    rw [idealPrimeExponent, Multiset.count_eq_zero,
      mem_normalizedFactors_iff (RMKummerConductor.m_ne_bot F h12 x)]
    exact fun h => hv (dvd_mul_of_dvd_left h.2 _)
  have hy : idealPrimeExponent v.asIdeal (RMKummerConductor.m F h12 y) = 0 := by
    rw [idealPrimeExponent, Multiset.count_eq_zero,
      mem_normalizedFactors_iff (RMKummerConductor.m_ne_bot F h12 y)]
    exact fun h => hv (dvd_mul_of_dvd_right h.2 _)
  have hz : idealPrimeExponent v.asIdeal (RMKummerConductor.m F h12 (x / y)) = 0 := by
    apply Nat.le_zero.mp
    apply (RMKummerCharacterAPI.local_conductor F h12 (x / y) v).2
    intro u hu
    apply MonoidHom.mem_ker.mpr
    rw [RMKummerLocalSquareLaws.lambda_div,
      RMKummerLeastLocalExponent.lambda_trivial_on_conductor_units F h12 x v u
        (by rwa [hx]),
      RMKummerLeastLocalExponent.lambda_trivial_on_conductor_units F h12 y v u
        (by rwa [hy]), inv_one, mul_one]
  intro hd
  have hmem := (mem_normalizedFactors_iff
    (RMKummerConductor.m_ne_bot F h12 (x / y))).mpr ⟨v.prime, hd⟩
  exact (Multiset.count_eq_zero.mp hz) hmem

theorem quotient_values (h12 : (primitiveRoots 12 F).Nonempty) (x y : Fˣ) :
    ∀ n : Ideal (𝓞 F), n ⊔
      (RMKummerConductor.m F h12 x * RMKummerConductor.m F h12 y) = ⊤ →
      RMKummerConductor.Xi F h12 (x / y) n =
        RMKummerConductor.Xi F h12 x n *
          (starRingEnd ℂ) (RMKummerConductor.Xi F h12 y n) := by
  intro n
  induction n using induction_on_prime with
  | h₁ => intro hn; simp
  | h₂ n hn =>
    have ht : n = ⊤ := Ideal.isUnit_iff.mp hn
    subst n
    intro hn
    simp only [RayClassCharacter.map_top', map_one, mul_one]
  | h₃ n p hn hp ih =>
    intro hcop
    have hncop : n ⊔
      (RMKummerConductor.m F h12 x * RMKummerConductor.m F h12 y) = ⊤ := by
      apply top_le_iff.mp
      rw [← hcop]
      exact sup_le_sup_right Ideal.mul_le_right _
    have hpcop : p ⊔
      (RMKummerConductor.m F h12 x * RMKummerConductor.m F h12 y) = ⊤ := by
      apply top_le_iff.mp
      rw [← hcop]
      exact sup_le_sup_right Ideal.mul_le_left _
    have hp0 : p ≠ ⊥ := hp.ne_zero
    let v : HeightOneSpectrum (𝓞 F) := ⟨p, Ideal.isPrime_of_prime hp, hp0⟩
    have hnot : ¬ v.asIdeal ∣
        RMKummerConductor.m F h12 x * RMKummerConductor.m F h12 y := by
      intro hd
      have hle : RMKummerConductor.m F h12 x * RMKummerConductor.m F h12 y ≤ p :=
        Ideal.dvd_iff_le.mp hd
      have ht : p = ⊤ := by rw [← hpcop, sup_eq_left.mpr hle]
      exact (Ideal.isPrime_of_prime hp).ne_top ht
    have hprime := RMKummerQuotientPrime.quotient_prime F h12 x y v
      (by rw [hp.dvd_mul]; exact not_or.mpr ⟨hnot, quotient_unramified h12 x y v hnot⟩)
    rw [(RMKummerConductor.Xi F h12 (x / y)).map_mul',
      (RMKummerConductor.Xi F h12 x).map_mul',
      (RMKummerConductor.Xi F h12 y).map_mul', map_mul, ih hncop]
    change RMKummerConductor.Xi F h12 (x / y) v.asIdeal * _ = _
    rw [hprime]
    change RMKummerConductor.Xi F h12 x p * (starRingEnd ℂ) (RMKummerConductor.Xi F h12 y p) * _ = _
    ring

theorem exteriorValues_of_formula
    (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (hformula : ∀ (c : Ideal (𝓞 F)) (hc : Squarefree c)
      (hcopc : c ⊔ uniformSquareUnitModulus A.Sf = ⊤)
      (d : Ideal (𝓞 F)) (hd : d ≠ ⊥)
      (hcopd : d ⊔ uniformSquareUnitModulus A.Sf = ⊤),
      RMKummerConductor.Xi F h12 (KummerSquarefreeMembers.generator A σ η hS C c hc hcopc) d =
        KummerExteriorValues.cubicSexticValue A σ η hS C
          (KummerSquarefreeMembers.exteriorIndex A c hc hcopc)
          (KummerExteriorValues.exteriorIndex A d hd hcopd)) :
    KummerExteriorValues.ExteriorValuesSpec A σ η hS C
      (fun x n => RMKummerConductor.Xi F h12 x n) := by
  refine ⟨hformula, ?_, ?_⟩
  · intro c hc hcopc d hd hcopd hcd
    have hz := (KummerExteriorValues.cubicSexticValue_shared_zero A σ η hS C
      (KummerSquarefreeMembers.exteriorIndex A c hc hcopc)
      (KummerExteriorValues.exteriorIndex A d hd hcopd) hcd).1
    exact ⟨(hformula c hc hcopc d hd hcopd).trans hz, hz⟩
  · intro c d hc hd hcopc hcopd hcd
    dsimp only
    rw [hformula c hc hcopc d (KummerSquarefreeMembers.exteriorIndex A d hd hcopd).property.1 hcopd,
      hformula d hd hcopd c (KummerSquarefreeMembers.exteriorIndex A c hc hcopc).property.1 hcopc]
    exact KummerExteriorValues.cubicSexticValue_symmetry A σ η hS C
      (KummerSquarefreeMembers.exteriorIndex A c hc hcopc)
      (KummerSquarefreeMembers.exteriorIndex A d hd hcopd) hcd

theorem productOutput_of_conductor
    (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (hcond : ∀ (a b : Ideal (𝓞 F)) (ha : Squarefree a)
      (hqa : a ⊔ uniformSquareUnitModulus A.Sf = ⊤)
      (hb : Squarefree b) (hqb : b ⊔ uniformSquareUnitModulus A.Sf = ⊤),
      a ⊔ b = ⊤ → C.integralCls a = C.integralCls b →
        RMKummerConductor.m F h12
          (KummerProductPrimitive.quotientRadical A σ η hS C a b ha hb hqa hqb) = a * b) :
    KummerProductPrimitive.ExactProductOutput A σ η hS C
      (RMKummerConductor.m F h12) (RMKummerConductor.Xi F h12) := by
  intro a b ha hqa hb hqb hab hcls
  refine ⟨hcond a b ha hqa hb hqb hab hcls, ?_, ?_⟩
  · exact KummerProductPrimitive.transport_primitive _ _ (actualCharacter_primitive h12 _)
  · intro n hn
    rw [KummerProductPrimitive.transport_apply]
    exact quotient_values h12 _ _ n hn

theorem exists_exactOutput_of_arithmetic_realizations (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (hprimitive : ∀ (c : Ideal (𝓞 F)) (hc : Squarefree c)
      (hcop : c ⊔ uniformSquareUnitModulus A.Sf = ⊤),
      (RMKummerConductor.Xi F h12
        (KummerSquarefreeMembers.generator A σ η hS C c hc hcop)).IsPrimitive)
    (hshape : ∀ (c : Ideal (𝓞 F)) (hc : Squarefree c)
      (hcop : c ⊔ uniformSquareUnitModulus A.Sf = ⊤),
      ∃ s : Ideal (𝓞 F), s ∣ uniformSquareUnitModulus A.Sf ∧
        RMKummerConductor.m F h12
          (KummerSquarefreeMembers.generator A σ η hS C c hc hcop) = c * s)
    (hvalues : KummerExteriorValues.ExteriorValuesSpec A σ η hS C
      (fun x n => RMKummerConductor.Xi F h12 x n))
    (hproduct : KummerProductPrimitive.ExactProductOutput A σ η hS C
      (RMKummerConductor.m F h12) (RMKummerConductor.Xi F h12)) :
    ∃ ℱ : QuadraticHeckeFamily F (uniformSquareUnitModulus A.Sf),
      ExactOutput h12 A σ η hS C ℱ := by
  let ℱ : QuadraticHeckeFamily F (uniformSquareUnitModulus A.Sf) := {
    cond := KummerFamilyAssembly.totalConductor A σ η hS C (RMKummerConductor.m F h12)
    χ := KummerFamilyAssembly.totalCharacter A σ η hS C
      (RMKummerConductor.m F h12) (RMKummerConductor.Xi F h12)
    primitive := by
      intro c hc hcop
      have h : KummerFamilyAssembly.Constrained A c := ⟨hc, hcop⟩
      constructor
      · rw [KummerFamilyAssembly.totalConductor_constrained _ _ _ _ _ _ _ h]
        exact RMKummerConductor.m_ne_bot F h12 _
      · simp only [KummerFamilyAssembly.totalCharacter, dif_pos h]
        exact KummerProductPrimitive.transport_primitive _ _ (hprimitive c hc hcop)
    quadratic := by
      intro c n hc hcop
      rw [KummerFamilyAssembly.totalCharacter_constrained_apply _ _ _ _ _ _ _ _ ⟨hc, hcop⟩]
      exact RMKummerSquareCharacter.Xi_cube F h12 _ n
    G := A.B₂ C.correction.B
    instGroup := inferInstance
    instFinite := A.B₂_finite C.correction.B
    cls := C.integralCls
    cls_top := C.integralCls_top
    cls_mul := C.integralCls_mul_uniform
    C := fun _ _ => 1
    C_sq := by intros; simp
    reciprocity := by
      intro a b ha hqa hb hqb hab
      rw [KummerFamilyAssembly.totalCharacter_constrained_apply _ _ _ _ _ _ _ _ ⟨ha, hqa⟩,
        KummerFamilyAssembly.totalCharacter_constrained_apply _ _ _ _ _ _ _ _ ⟨hb, hqb⟩,
        mul_one]
      exact hvalues.2.2 a b ha hb hqa hqb hab
    product_primitive := by
      intro a b ha hqa hb hqb hab hcls
      obtain ⟨hcond, hp, hv⟩ := hproduct a b ha hqa hb hqb hab hcls
      refine ⟨KummerProductPrimitive.transport hcond
        (RMKummerConductor.Xi F h12
          (KummerProductPrimitive.quotientRadical A σ η hS C a b ha hb hqa hqb)), hp, ?_⟩
      intro n hn
      rw [KummerFamilyAssembly.totalConductor_constrained _ _ _ _ _ _ _ ⟨ha, hqa⟩,
        KummerFamilyAssembly.totalConductor_constrained _ _ _ _ _ _ _ ⟨hb, hqb⟩] at hn
      rw [KummerFamilyAssembly.totalCharacter_constrained_apply _ _ _ _ _ _ _ _ ⟨ha, hqa⟩,
        KummerFamilyAssembly.totalCharacter_constrained_apply _ _ _ _ _ _ _ _ ⟨hb, hqb⟩]
      exact hv n hn }
  refine ⟨ℱ, rfl, ?_, rfl, HEq.rfl, ?_, ?_, ?_, ?_, ?_, hproduct, ?_, ?_, ?_⟩
  · intro c n; rfl
  · intro c; rfl
  · intro g h; rfl
  · intro c hc hcop
    obtain ⟨s, hs, heq⟩ := hshape c hc hcop
    refine ⟨s, hs, ?_⟩
    exact (KummerFamilyAssembly.totalConductor_constrained _ _ _ _ _ _ _ ⟨hc, hcop⟩).trans heq
  · intro c hc hcop d hd hcopd
    change KummerFamilyAssembly.totalCharacter _ _ _ _ _ _ _ _ _ = _
    rw [KummerFamilyAssembly.totalCharacter_constrained_apply _ _ _ _ _ _ _ _ ⟨hc, hcop⟩]
    exact hvalues.1 c hc hcop d hd hcopd
  · intro c hc hcop d hd hcopd hcd
    change KummerFamilyAssembly.totalCharacter _ _ _ _ _ _ _ _ _ = _
    rw [KummerFamilyAssembly.totalCharacter_constrained_apply _ _ _ _ _ _ _ _ ⟨hc, hcop⟩]
    exact (hvalues.2.1 c hc hcop d hd hcopd hcd).1
  · exact totalConductor_top h12 A σ η hS C
  · exact totalCharacter_top_apply h12 A σ η hS C
  · intro c hc
    exact ⟨KummerFamilyAssembly.totalConductor_unconstrained _ _ _ _ _ _ _ hc,
      fun n => KummerFamilyAssembly.totalCharacter_unconstrained_apply _ _ _ _ _ _ _ _ hc n⟩

theorem exists_actualKummerFamily (h12 : (primitiveRoots 12 F).Nonempty)
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS) :
    uniformSquareUnitModulus A.Sf ≠ ⊥ ∧
    (∀ v : HeightOneSpectrum (𝓞 F),
      uniformSquareUnitModulus A.Sf ≤ v.asIdeal ↔ v ∈ A.Sf) ∧
    ∃ ℱ : QuadraticHeckeFamily F (uniformSquareUnitModulus A.Sf),
      ExactOutput h12 A σ η hS C ℱ := by
  obtain ⟨hne, hsupport, _⟩ := uniformSquareUnitModulus_spec A.Sf
  refine ⟨hne, hsupport, ?_⟩
  apply exists_exactOutput_of_arithmetic_realizations h12 A σ η hS C
  · intro c hc hcop
    exact actualCharacter_primitive h12 _
  · exact RMKummerConductorArithmetic.squarefree_conductor_shape h12 A σ η hS C
  · apply exteriorValues_of_formula h12 A σ η hS C
    exact RMKummerConductorArithmetic.actual_cubic_sextic_value h12 A σ η hS C
  · apply productOutput_of_conductor h12 A σ η hS C
    exact RMKummerConductorArithmetic.equal_class_quotient_conductor h12 A σ η hS C

end RMKummerFamily
end
end DedekindZetaZeroFree

end
