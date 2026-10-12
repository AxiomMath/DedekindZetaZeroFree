module

public import DedekindZetaZeroFree.ZeroDetection.Conductors.LocalFrequencyCompatibility

@[expose] public section

section

namespace DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter.ExteriorCharacterSteps

open scoped NumberField Classical
open NumberField IsDedekindDomain RayClassBridge
open ClassFieldTheory.GlobalClassFieldComparison

noncomputable section

private theorem exp_zero_iff (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    idealPrimeExponent v.asIdeal I = 0 ↔ ¬ I ≤ v.asIdeal := by
  rw [idealPrimeExponent, Multiset.count_eq_zero,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff hI]
  simp [v.prime, Ideal.dvd_iff_le]

private theorem exp_mul (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    idealPrimeExponent v.asIdeal (I * J) =
      idealPrimeExponent v.asIdeal I + idealPrimeExponent v.asIdeal J := by
  simp [idealPrimeExponent, UniqueFactorizationMonoid.normalizedFactors_mul hI hJ,
    Multiset.count_add]

private theorem le_pow_exp (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    I ≤ v.asIdeal ^ idealPrimeExponent v.asIdeal I := by
  rw [← Ideal.dvd_iff_le, pow_dvd_iff_le_emultiplicity,
    UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hI]
  simp [idealPrimeExponent]

private theorem ratio_higher (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hav : a ∉ v.asIdeal) (hbv : b ∉ v.asIdeal) (k : ℕ)
    (hab : a - b ∈ v.asIdeal ^ k) :
    integralElementLocalUnit F v a ha / integralElementLocalUnit F v b hb ∈
      RayClass.localHigherUnitGroup v k := by
  let aa : v.adicCompletionIntegers F := algebraMap _ _ a
  let bb : v.adicCompletionIntegers F := algebraMap _ _ b
  have hua : IsUnit aa := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a) = 1
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    exact (v.valuedAdicCompletion_eq_valuation' (K := F) (a : F)).trans
      (v.valuation_eq_one_iff_notMem.mpr hav)
  have hub : IsUnit bb := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) b) = 1
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    exact (v.valuedAdicCompletion_eq_valuation' (K := F) (b : F)).trans
      (v.valuation_eq_one_iff_notMem.mpr hbv)
  change _ ∈ ClassFieldTheory.rayLocalHigherUnitGroup v k
  rw [ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff]
  refine ⟨hua.unit / hub.unit, ?_, ?_⟩
  · change Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom
        (hua.unit / hub.unit) = _
    rw [map_div]
    have haeq : Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom hua.unit =
        integralElementLocalUnit F v a ha := by
      apply Units.ext
      change (↑hua.unit : v.adicCompletionIntegers F).val = _
      rw [hua.unit_spec]
      rfl
    have hbeq : Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom hub.unit =
        integralElementLocalUnit F v b hb := by
      apply Units.ext
      change (↑hub.unit : v.adicCompletionIntegers F).val = _
      rw [hub.unit_spec]
      rfl
    rw [haeq, hbeq]
  · have hmem : aa - bb ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ k := by
      simpa only [aa, bb, map_sub] using (CRT_completed_power_mem_iff F v (a - b) k).mpr hab
    have heq : ((hua.unit / hub.unit : (v.adicCompletionIntegers F)ˣ) :
        v.adicCompletionIntegers F) - 1 = (aa - bb) * ↑(hub.unit⁻¹) := by
      simp only [div_eq_mul_inv, Units.val_mul, hua.unit_spec]
      have hbi : bb * (↑(hub.unit⁻¹) : v.adicCompletionIntegers F) = 1 := by
        simpa only [hub.unit_spec] using hub.unit.mul_inv
      rw [sub_mul, hbi]
    rw [heq]
    exact Ideal.mul_mem_right _ _ hmem

theorem crt_removed_ratio_mem_primeTo
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (f fS qO : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (hsplit : FixedSResidue.ConductorSplit A f fS qO)
    (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0)
    (haunit : IsUnit (Ideal.Quotient.mk (FixedSResidue.residueModulus A qO)
      (algebraMap (𝓞 F) A.R a)))
    (hba : b - a ∈ qO) (hbS : b - 1 ∈ fS) :
    IdeleGroup.principalIdele F
        (Units.mk0 (a : F) (by exact_mod_cast ha) /
          Units.mk0 (b : F) (by exact_mod_cast hb)) /
      (∏ v : {v // v ∈ A.Sf}, IdeleGroup.finitePlaceIdele v.val
        (integralElementLocalUnit F v.val a ha)) ∈
      RayClass.idelePrimeToModulusSubgroup
        (rayClassModulusToOriginal F (narrowIdealModulus F f hf)) := by
  classical
  let m := rayClassModulusToOriginal F (narrowIdealModulus F f hf)
  have hme (v : HeightOneSpectrum (𝓞 F)) : m.finitePart v = idealPrimeExponent v.asIdeal f :=
    M_finitePart F f hf v
  have haqo : Ideal.span {a} ⊔ qO = ⊤ := by
    have hmap : Ideal.map (algebraMap (𝓞 F) A.R) (Ideal.span {a} ⊔ qO) = ⊤ := by
      rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
      have hu := Ideal.span_singleton_eq_top.mpr haunit
      have hh := congrArg (Ideal.comap (Ideal.Quotient.mk (FixedSResidue.residueModulus A qO))) hu
      rw [← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_quotientMk,
        Ideal.comap_top] at hh
      simpa only [FixedSResidue.residueModulus, sup_comm] using hh
    have hh := congrArg (fun I : Ideal A.R => I.under (𝓞 F)) hmap
    rw [SIntegerLocalization.under_map_exterior A.Sf (Ideal.span {a} ⊔ qO) (by
      change (Ideal.span {a} ⊔ qO) ⊔ A.cS = ⊤
      rw [sup_assoc, hsplit.2.2.2.2.2, sup_top_eq])] at hh
    simpa only [Ideal.comap_top] using hh
  have hinsert (v : HeightOneSpectrum (𝓞 F)) :
      IdeleGroup.finiteComponent v
        (∏ w : {w // w ∈ A.Sf}, IdeleGroup.finitePlaceIdele w.val
          (integralElementLocalUnit F w.val a ha)) =
      if v ∈ A.Sf then integralElementLocalUnit F v a ha else 1 := by
    rw [map_prod]
    by_cases hv : v ∈ A.Sf
    · rw [if_pos hv]
      rw [Finset.prod_eq_single (⟨v, hv⟩ : {w // w ∈ A.Sf})]
      · exact IdeleGroup.finitePlaceIdele_finiteComponent_same v _
      · intro w _ hne
        exact IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _ _ _ (by
          intro he; apply hne; exact Subtype.ext he.symm)
      · simp
    · rw [if_neg hv]
      apply Finset.prod_eq_one
      intro w _
      exact IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _ _ _ (by
        intro he; exact hv (he ▸ w.property))
  have hprincipal (c : 𝓞 F) (hc : c ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
      IdeleGroup.finiteComponent v (IdeleGroup.principalIdele F
        (Units.mk0 (c : F) (by exact_mod_cast hc))) = integralElementLocalUnit F v c hc := by
    apply Units.ext
    rfl
  let z := IdeleGroup.principalIdele F
      (Units.mk0 (a : F) (by exact_mod_cast ha) / Units.mk0 (b : F) (by exact_mod_cast hb)) /
    (∏ w : {w // w ∈ A.Sf}, IdeleGroup.finitePlaceIdele w.val
      (integralElementLocalUnit F w.val a ha))
  constructor
  · change z.1 ∈ m.infiniteCongruenceSubgroup
    rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff_local]
    intro w
    rw [RayClass.Modulus.localInfiniteCongruenceSubgroup_of_not_isReal m w
      (InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place w))]
    trivial
  · intro v hv
    change z.2 v ∈ RayClass.localHigherUnitGroup v (m.finitePart v)
    rw [← IdeleGroup.finiteComponent_apply]
    dsimp only [z]
    rw [map_div, map_div, map_div, hprincipal a ha v, hprincipal b hb v, hinsert, hme]
    have hpos : idealPrimeExponent v.asIdeal f ≠ 0 := by
      rw [← hme]
      exact Finsupp.mem_support_iff.mp hv
    by_cases hvs : v ∈ A.Sf
    · rw [if_pos hvs]
      have hcS : A.cS ≤ v.asIdeal := by
        change A.Sf.prod (fun w => w.asIdeal) ≤ v.asIdeal
        exact Ideal.prod_le_inf.trans (Finset.inf_le hvs)
      have hq0 : idealPrimeExponent v.asIdeal qO = 0 := by
        apply (exp_zero_iff F v qO hsplit.2.2.1).mpr
        intro hq
        exact v.isPrime.ne_top (top_le_iff.mp (hsplit.2.2.2.2.2 ▸ sup_le hq hcS))
      have hexp : idealPrimeExponent v.asIdeal f = idealPrimeExponent v.asIdeal fS := by
        rw [hsplit.2.2.2.1, exp_mul F v fS qO hsplit.2.1 hsplit.2.2.1, hq0, add_zero]
      have hbpow : b - 1 ∈ v.asIdeal ^ idealPrimeExponent v.asIdeal f := by
        rw [hexp]
        exact le_pow_exp F v fS hsplit.2.1 hbS
      have hbv : b ∉ v.asIdeal := by
        intro hbmem
        have hpowle := Ideal.pow_le_self (I := v.asIdeal) hpos
        have h1 := v.asIdeal.sub_mem hbmem (hpowle hbpow)
        have : (1 : 𝓞 F) ∈ v.asIdeal := by simpa using h1
        exact v.isPrime.ne_top (v.asIdeal.eq_top_iff_one.mpr this)
      have hhigh := integral_unit_mem_higherUnits F v b hb hbv _ hbpow
      have hbmem : integralElementLocalUnit F v b hb ∈ RayClass.localHigherUnitGroup v
          (idealPrimeExponent v.asIdeal f) := by
        change _ ∈ ClassFieldTheory.rayLocalHigherUnitGroup v _
        rwa [ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff]
      convert (RayClass.localHigherUnitGroup v (idealPrimeExponent v.asIdeal f)).inv_mem hbmem using 1
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    · rw [if_neg hvs, div_one]
      have hs0 : idealPrimeExponent v.asIdeal fS = 0 := by
        apply (exp_zero_iff F v fS hsplit.2.1).mpr
        exact fun hs => hvs (hsplit.2.2.2.2.1 v hs)
      have hexp : idealPrimeExponent v.asIdeal f = idealPrimeExponent v.asIdeal qO := by
        rw [hsplit.2.2.2.1, exp_mul F v fS qO hsplit.2.1 hsplit.2.2.1, hs0, zero_add]
      have hqle : qO ≤ v.asIdeal := by
        by_contra hn
        exact hpos (hexp.trans ((exp_zero_iff F v qO hsplit.2.2.1).mpr hn))
      have hav : a ∉ v.asIdeal := by
        intro hamem
        have hspan : Ideal.span {a} ≤ v.asIdeal := Ideal.span_singleton_le_iff_mem _ |>.mpr hamem
        exact v.isPrime.ne_top (top_le_iff.mp (haqo ▸ sup_le hspan hqle))
      have hbv : b ∉ v.asIdeal := by
        intro hbmem
        exact hav (by
          have := v.asIdeal.sub_mem hbmem (hqle hba)
          simpa using this)
      apply ratio_higher F v a b ha hb hav hbv
      rw [hexp]
      exact le_pow_exp F v qO hsplit.2.2.1 (by simpa only [neg_sub] using qO.neg_mem hba)

end
end DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter.ExteriorCharacterSteps

end

section

namespace DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter.ExteriorCharacterSteps

open scoped NumberField Classical
open NumberField IsDedekindDomain RayClassBridge

noncomputable section

theorem removed_principal_integral_ratio_ideal
    (F : Type) [Field F] [NumberField F]
    (x : Fˣ) (s : IdeleGroup F) (b : 𝓞 F) (hb : b ≠ 0) :
    IdeleGroup.fractionalIdeal
        (IdeleGroup.principalIdele F
          (x / Units.mk0 (b : F) (by exact_mod_cast hb)) / s) =
      IdeleGroup.fractionalIdeal (IdeleGroup.principalIdele F x / s) /
        integralUnit F (Ideal.span {b}) (by simpa using hb) := by

  have hkey :
      toPrincipalIdeal (𝓞 F) F (Units.mk0 (b : F) (by exact_mod_cast hb)) =
        integralUnit F (Ideal.span {b}) (by simpa using hb) := by
    refine Units.ext ?_
    rw [coe_toPrincipalIdeal, RayClassBridge.integralUnit_val,
      FractionalIdeal.coeIdeal_span_singleton, Units.val_mk0]

  simp only [map_div, IdeleGroup.fractionalIdeal_principalIdele, hkey]
  rw [div_div, div_div, mul_comm]

end
end DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter.ExteriorCharacterSteps

end

section

namespace DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter.ExteriorCharacterSteps

open scoped NumberField Classical
open NumberField IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

private theorem count_nf (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {I : Ideal (𝓞 F)} (hI : I ≠ 0) :
    FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (idealPrimeExponent v.asIdeal I : ℤ) := by
 rw [FractionalIdeal.count_coe F v hI]
 unfold idealPrimeExponent
 congr 1
 open Associates in
 rw [factors_mk _ hI, count_some (irreducible_mk.mpr v.irreducible),
    ← Multiset.count_map_eq_count' _ _ Subtype.val_injective, map_subtype_coe_factors',
    factors_eq_normalizedFactors, ← Multiset.count_map_eq_count' _ _ (mk_injective (M := Ideal (𝓞 F)))]

theorem exterior_removed_idele_ideal
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (a : 𝓞 F) (ha : a ≠ 0) (e : A.Exterior)
    (he : Ideal.span {algebraMap (𝓞 F) A.R a} = A.extendIdeal e)
    (z : _root_.IdeleGroup F)
    (hzS : ∀ v ∈ A.Sf, IdeleGroup.finiteComponent v z = 1)
    (hzext : ∀ v, v ∉ A.Sf → IdeleGroup.finiteComponent v z =
      integralElementLocalUnit F v a ha) :
    IdeleGroup.fractionalIdeal z = RayClassBridge.integralUnit F e.val e.property.1 := by
  apply FractionalIdealGroup.ext_count
  intro v
  have hc : FractionalIdeal.count F v
      (IdeleGroup.fractionalIdeal z : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (FiniteIdeleGroup.localOrder v (IdeleGroup.finiteComponent v z)).toAdd := by
    change FractionalIdeal.count F v
      (((FractionalIdealGroup.factorization (K := F)) (FiniteIdeleGroup.valuationVector z.2) :
        FractionalIdealGroup F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = _
    rw [FractionalIdealGroup.count_factorization, FiniteIdeleGroup.valuationVector_apply]
    rfl
  rw [hc]
  change _ = FractionalIdeal.count F v (e.val : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  rw [count_nf F v e.property.1]
  by_cases hv : v ∈ A.Sf
  · rw [hzS v hv]
    have hcop := (A.exterior_iff ⟨e.val, e.property.1⟩).mp e.property.2 v hv
    have hn : v.asIdeal ∉ normalizedFactors e.val := by
      intro hn
      have hd := Ideal.dvd_iff_le.mp ((mem_normalizedFactors_iff e.property.1).mp hn).2
      exact v.isPrime.ne_top (top_le_iff.mp (hcop ▸ sup_le hd le_rfl))
    simp [idealPrimeExponent, Multiset.count_eq_zero.mpr hn]
  · rw [hzext v hv, FiniteIdeleGroup.localOrder_apply]
    have hval := SIntegerLocalization.generator_completion_valuation A.Sf e.val e.property.1
      (algebraMap (𝓞 F) A.R a)
      ((FaithfulSMul.algebraMap_injective (𝓞 F) A.R).ne ha) he
      (Units.mk0 (a : F) (by exact_mod_cast ha)) rfl v hv
    change Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = _ at hval
    change -WithZero.log (Valued.v (algebraMap F (v.adicCompletion F) (a : F))) = _
    rw [hval, WithZero.log_exp, neg_neg]

open RayClassBridge ClassFieldTheory.GlobalClassFieldComparison

theorem finite_component_eq_idelic
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (omega : PrimitiveFrequencyCharacter F)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (hlocal : ∀ v : {v // v ∈ A.Sf},
      ∃ delta : (v.val.adicCompletion F)ˣ →ₜ* ℂˣ,
        delta.toMonoidHom = sigma.2 v ∧ IsFrequencyLocalComponent F omega v.val delta)
    (v : {v // v ∈ A.Sf}) (u : (v.val.adicCompletion F)ˣ) :
    sigma.2 v u = ideleClassCharacter F
      (primitive12_totallyComplex F A.zeta12 A.primitive_zeta12)
      omega.conductor omega.conductor_ne_zero omega.character
      (IdeleGroup.finitePlaceIdeleClass v.val u) := by
  let hc := primitive12_totallyComplex F A.zeta12 A.primitive_zeta12
  obtain ⟨delta, hdelta, hspec⟩ := hlocal v
  have hcan : Conductor.Raw.IsFrequencyLocalComponent F omega v.val
      (Conductor.canonicalFrequencyLocalCharacter F hc omega v.val) :=
    Conductor.LocalTwistSteps.idelic_restriction_is_raw_local_component F hc omega
      v.val _ (by intro u; rfl)
  have heq := Conductor.LocalTwistSteps.raw_local_component_unique F omega v.val
    delta (Conductor.canonicalFrequencyLocalCharacter F hc omega v.val) hspec hcan
  rw [← hdelta, heq]
  rfl

def finiteDiagonalIdele
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F) (x : Fˣ) :
    IdeleGroup F :=
  ∏ v : {v // v ∈ A.Sf}, IdeleGroup.finitePlaceIdele v.val
    (ClassFieldTheory.finitePlaceUnitEmbedding v.val x)

theorem localInverseProduct_eq_finiteDiagonal
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (omega : PrimitiveFrequencyCharacter F)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (hinfinite : ∀ w : InfinitePlace F, sigma.1 w = 1)
    (hlocal : ∀ v : {v // v ∈ A.Sf},
      ∃ delta : (v.val.adicCompletion F)ˣ →ₜ* ℂˣ,
        delta.toMonoidHom = sigma.2 v ∧ IsFrequencyLocalComponent F omega v.val delta)
    (n : FixedSResidue.NonzeroSInteger A) :
    FixedSResidue.localInverseProduct A sigma n =
      ((ideleClassCharacter F
        (primitive12_totallyComplex F A.zeta12 A.primitive_zeta12)
        omega.conductor omega.conductor_ne_zero omega.character
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
          (finiteDiagonalIdele F A (FixedSResidue.fieldUnit A n))) : ℂ))⁻¹ := by
  simp only [FixedSResidue.localInverseProduct, hinfinite, MonoidHom.one_apply,
    Units.val_one, inv_one, Finset.prod_const_one, one_mul,
    finiteDiagonalIdele, map_prod, Units.coe_prod, Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  rw [finite_component_eq_idelic F A omega sigma hlocal v]
  rfl

theorem primeTo_idele_evaluation (F : Type) [Field F] [NumberField F] (hc : NumberField.IsTotallyComplex F)
 (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (η : RayClassCharacter F m)
 (a : IdeleGroup F) (ha : a ∈ RayClass.idelePrimeToModulusSubgroup
  (rayClassModulusToOriginal F (narrowIdealModulus F m hm))) :
 ideleClassCharacter F hc m hm η (QuotientGroup.mk' (IdeleGroup.principalSubgroup F) a) =
 fractionalCharacter F m hm η
   ⟨IdeleGroup.fractionalIdeal a, RayClass.fractionalIdeal_mem_primeToModulusIdeals _ a ha⟩ := by
 let M := narrowIdealModulus F m hm
 let M' := rayClassModulusToOriginal F M
 let A : RayClass.idelePrimeToModulusSubgroup M' := ⟨a,ha⟩
 let I : ClassFieldTheory.rayClassPrimeToIdeals M :=
   ⟨IdeleGroup.fractionalIdeal a, RayClass.fractionalIdeal_mem_primeToModulusIdeals _ a ha⟩
 have he : rayClassGroupEquivOriginalIdele F M
     (QuotientGroup.mk' (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo M) I) =
       QuotientGroup.mk' M'.congruenceSubgroup
         (QuotientGroup.mk' (IdeleGroup.principalSubgroup F) a) := by
   apply (RayClass.rayClassGroupEquivIdealRayClassGroup M').injective
   simp only [rayClassGroupEquivOriginalIdele, MulEquiv.trans_apply,
      MulEquiv.apply_symm_apply]
   have hI : rayClassGroupEquivOriginal F M
       (QuotientGroup.mk' (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo M) I) =
       RayClass.idealRayProjection M' A := by
     rfl
   rw [hI]
   symm
   rw [RayClass.rayClassGroupEquivIdealRayClassGroup, MulEquiv.trans_apply,
     MulEquiv.trans_apply]
   have hproj : RayClass.rayClassGroupEquivIdeleQuotient M'
       (QuotientGroup.mk' M'.congruenceSubgroup
         (QuotientGroup.mk' (IdeleGroup.principalSubgroup F) a)) =
       RayClass.primeToRayClassProjection M' A := by
     rfl
   rw [hproj, ← RayClass.quotientRaySubgroupEquivIdeleRayQuotient_mk,
     MulEquiv.symm_apply_apply, RayClass.quotientRaySubgroupEquivIdealRayClassGroup_mk]
   exact (MulEquiv.apply_symm_apply _ _).symm
 change rayCharacter F hc m hm η
   ((rayClassGroupEquivOriginalIdele F M).symm
     (QuotientGroup.mk' M'.congruenceSubgroup
       (QuotientGroup.mk' (IdeleGroup.principalSubgroup F) a))) = _
 rw [← he, MulEquiv.symm_apply_apply]
 exact DFunLike.congr_fun (rayCharacter_comp_quotient F hc m hm η) I

theorem principal_ratio_transfer
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (omega : PrimitiveFrequencyCharacter F)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (hinfinite : ∀ w : InfinitePlace F, sigma.1 w = 1)
    (hlocal : ∀ v : {v // v ∈ A.Sf},
      ∃ delta : (v.val.adicCompletion F)ˣ →ₜ* ℂˣ,
        delta.toMonoidHom = sigma.2 v ∧ IsFrequencyLocalComponent F omega v.val delta)
    (n : FixedSResidue.NonzeroSInteger A) (y : Fˣ)
    (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hcI : I ⊔ omega.conductor = ⊤) (hcJ : J ⊔ omega.conductor = ⊤)
    (hprime :
      IdeleGroup.principalIdele F (FixedSResidue.fieldUnit A n / y) /
        finiteDiagonalIdele F A (FixedSResidue.fieldUnit A n) ∈
      RayClass.idelePrimeToModulusSubgroup
        (rayClassModulusToOriginal F
          (narrowIdealModulus F omega.conductor omega.conductor_ne_zero)))
    (hideal :
      IdeleGroup.fractionalIdeal
        (IdeleGroup.principalIdele F (FixedSResidue.fieldUnit A n / y) /
          finiteDiagonalIdele F A (FixedSResidue.fieldUnit A n)) =
        integralUnit F I hI / integralUnit F J hJ) :
    omega.character I = FixedSResidue.localInverseProduct A sigma n * omega.character J := by
  let hc := primitive12_totallyComplex F A.zeta12 A.primitive_zeta12
  let z := IdeleGroup.principalIdele F (FixedSResidue.fieldUnit A n / y) /
    finiteDiagonalIdele F A (FixedSResidue.fieldUnit A n)
  have heval := primeTo_idele_evaluation F hc omega.conductor
    omega.conductor_ne_zero omega.character z hprime
  have heq : (⟨IdeleGroup.fractionalIdeal z,
      RayClass.fractionalIdeal_mem_primeToModulusIdeals _ z hprime⟩ :
      ClassFieldTheory.rayClassPrimeToIdeals
        (narrowIdealModulus F omega.conductor omega.conductor_ne_zero)) =
      integralPrimeTo F omega.conductor omega.conductor_ne_zero I hI hcI /
        integralPrimeTo F omega.conductor omega.conductor_ne_zero J hJ hcJ := by
    apply Subtype.ext
    exact hideal
  rw [heq] at heval
  have hprin : QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
      (IdeleGroup.principalIdele F (FixedSResidue.fieldUnit A n / y)) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨_, rfl⟩
  have hzclass : QuotientGroup.mk' (IdeleGroup.principalSubgroup F) z =
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
        (finiteDiagonalIdele F A (FixedSResidue.fieldUnit A n)))⁻¹ := by
    change QuotientGroup.mk' (IdeleGroup.principalSubgroup F) (_ / _) = _
    rw [map_div, hprin, one_div]
  rw [hzclass, map_inv, map_div] at heval
  have hval := congrArg (fun u : ℂˣ => (u : ℂ)) heval
  rw [Units.val_inv_eq_inv_val, Units.val_div_eq_div_val,
    fractionalCharacter_integral, fractionalCharacter_integral,
    ← localInverseProduct_eq_finiteDiagonal F A omega sigma hinfinite hlocal n] at hval
  have hJval : omega.character J ≠ 0 :=
    (rayClassCharacter_ne_zero_iff F omega.conductor omega.character J).mpr ⟨hJ, hcJ⟩
  exact (div_eq_iff hJval).mp hval.symm

theorem sFiniteInsertion_component (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
  (x : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
  IdeleGroup.finiteComponent v
    (∏ w : {w // w ∈ A.Sf}, IdeleGroup.finitePlaceIdele w.val
      (ClassFieldTheory.finitePlaceUnitEmbedding w.val x)) =
    if v ∈ A.Sf then ClassFieldTheory.finitePlaceUnitEmbedding v x else 1 := by
  rw [map_prod]
  by_cases hv : v ∈ A.Sf
  · rw [if_pos hv]
    rw [Finset.prod_eq_single (⟨v, hv⟩ : {w // w ∈ A.Sf})]
    · exact IdeleGroup.finitePlaceIdele_finiteComponent_same v _
    · intro w hw hne
      apply IdeleGroup.finitePlaceIdele_finiteComponent_of_ne
      intro he
      exact hne (Subtype.ext he.symm)
    · simp
  · rw [if_neg hv]
    apply Finset.prod_eq_one
    intro w hw
    apply IdeleGroup.finitePlaceIdele_finiteComponent_of_ne
    intro he
    exact hv (he ▸ w.property)

theorem s_removed_principal_ideal (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
  (a : 𝓞 F) (ha : a ≠ 0) (e : A.Exterior)
  (he : Ideal.span {algebraMap (𝓞 F) A.R a} = A.extendIdeal e) :
  IdeleGroup.fractionalIdeal
    (IdeleGroup.principalIdele F (Units.mk0 (a : F) (by exact_mod_cast ha)) /
      ∏ w : {w // w ∈ A.Sf}, IdeleGroup.finitePlaceIdele w.val
        (integralElementLocalUnit F w.val a ha)) =
    RayClassBridge.integralUnit F e.val e.property.1 := by
  let x : Fˣ := Units.mk0 (a : F) (by exact_mod_cast ha)
  have hu (v : HeightOneSpectrum (𝓞 F)) :
      integralElementLocalUnit F v a ha = ClassFieldTheory.finitePlaceUnitEmbedding v x := by
    apply Units.ext
    rfl
  simp_rw [hu]
  apply exterior_removed_idele_ideal F A a ha e he
  · intro v hv
    rw [map_div, sFiniteInsertion_component, if_pos hv]
    have hp : IdeleGroup.finiteComponent v (IdeleGroup.principalIdele F x) =
      ClassFieldTheory.finitePlaceUnitEmbedding v x := by
      apply Units.ext
      rfl
    rw [hp, div_self']
  · intro v hv
    rw [map_div, sFiniteInsertion_component, if_neg hv, div_one, hu]
    apply Units.ext
    rfl

private theorem unit_quotient_coprime {R : Type*} [CommRing R]
    (q : Ideal R) (x : R) :
    IsUnit (Ideal.Quotient.mk q x) ↔ Ideal.span {x} ⊔ q = ⊤ := by
  constructor
  · intro h
    have he : Ideal.map (Ideal.Quotient.mk q) (Ideal.span {x} ⊔ q) = ⊤ := by
      simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton,
        Ideal.map_quotient_self, sup_bot_eq]
      exact Ideal.span_singleton_eq_top.mpr h
    have hh := congrArg (Ideal.comap (Ideal.Quotient.mk q)) he
    rw [Ideal.comap_map_quotientMk, Ideal.comap_top, sup_left_comm, sup_idem] at hh
    exact hh
  · intro hc
    have hh := congrArg (Ideal.map (Ideal.Quotient.mk q)) hc
    simpa only [Ideal.map_sup, Ideal.map_top, Ideal.map_quotient_self,
      sup_bot_eq, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top] using hh

private theorem exterior_map_top_reflect
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (J : Ideal (𝓞 F)) (hJ : J ⊔ A.cS = ⊤)
    (hmap : Ideal.map (algebraMap (𝓞 F) A.R) J = ⊤) : J = ⊤ := by
  have h := congrArg (fun I : Ideal A.R => I.under (𝓞 F)) hmap
  rw [SIntegerLocalization.under_map_exterior A.Sf J hJ] at h
  simpa only [Ideal.comap_top] using h

private theorem exterior_coprime_supported
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (J : Ideal (𝓞 F)) (hJ0 : J ≠ ⊥) (hJ : J ⊔ A.cS = ⊤)
    (fS : Ideal (𝓞 F))
    (hsupp : ∀ v : HeightOneSpectrum (𝓞 F), fS ≤ v.asIdeal → v ∈ A.Sf) :
    J ⊔ fS = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (J ⊔ fS) hne
  have hM0 : M ≠ ⊥ := ne_bot_of_le_ne_bot hJ0 (le_sup_left.trans hle)
  let v : HeightOneSpectrum (𝓞 F) := ⟨M, hM.isPrime, hM0⟩
  have hv : v ∈ A.Sf := hsupp v (le_sup_right.trans hle)
  have hc : A.cS ≤ M := by
    change A.Sf.prod (fun w => w.asIdeal) ≤ v.asIdeal
    exact (Ideal.prod_le_inf : A.Sf.prod (fun w => w.asIdeal) ≤ A.Sf.inf (fun w => w.asIdeal)).trans
      (Finset.inf_le hv)
  have htop : (⊤ : Ideal (𝓞 F)) ≤ M := by
    rw [← hJ]
    exact sup_le (le_sup_left.trans hle) hc
  exact hM.ne_top (top_unique htop)

theorem integral_exterior_crt_coprime
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (f fS qO : Ideal (𝓞 F)) (hsplit : FixedSResidue.ConductorSplit A f fS qO)
    (a b : 𝓞 F) (hb : b ≠ 0)
    (haunit : IsUnit (Ideal.Quotient.mk (FixedSResidue.residueModulus A qO)
      (algebraMap (𝓞 F) A.R a)))
    (hba : b - a ∈ qO) (hbS : b - 1 ∈ fS)
    (hbext : Ideal.span {b} ⊔ A.cS = ⊤)
    (e : A.Exterior)
    (he : Ideal.span {algebraMap (𝓞 F) A.R a} = A.extendIdeal e) :
    e.val ⊔ f = ⊤ ∧ Ideal.span {b} ⊔ f = ⊤ := by
  have heq : e.val ⊔ qO = ⊤ := by
    apply exterior_map_top_reflect F A _ (by rw [sup_assoc, sup_left_comm, e.property.2, sup_top_eq])
    rw [Ideal.map_sup]
    change A.extendIdeal e ⊔ FixedSResidue.residueModulus A qO = ⊤
    rw [← he]
    exact (unit_quotient_coprime _ _).mp haunit
  have hbunit : IsUnit (Ideal.Quotient.mk (FixedSResidue.residueModulus A qO)
      (algebraMap (𝓞 F) A.R b)) := by
    have hcong : Ideal.Quotient.mk (FixedSResidue.residueModulus A qO)
        (algebraMap (𝓞 F) A.R b) = Ideal.Quotient.mk (FixedSResidue.residueModulus A qO)
        (algebraMap (𝓞 F) A.R a) := by
      apply Ideal.Quotient.eq.mpr
      rw [← map_sub]
      exact Ideal.mem_map_of_mem _ hba
    rw [hcong]
    exact haunit
  have hbq : Ideal.span {b} ⊔ qO = ⊤ := by
    apply exterior_map_top_reflect F A _ (by rw [sup_assoc, sup_left_comm, hbext, sup_top_eq])
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    exact (unit_quotient_coprime _ _).mp hbunit
  have hes : e.val ⊔ fS = ⊤ := exterior_coprime_supported F A e.val e.property.1
    e.property.2 fS hsplit.2.2.2.2.1
  have hbs : Ideal.span {b} ⊔ fS = ⊤ :=
    RayClassBridge.span_add_modulus_eq_top_of_sub_one_mem F fS b hbS
  rw [hsplit.2.2.2.1]
  exact ⟨Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_iff_sup_eq.mpr hes).mul_right
      (Ideal.isCoprime_iff_sup_eq.mpr heq)),
    Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_iff_sup_eq.mpr hbs).mul_right
      (Ideal.isCoprime_iff_sup_eq.mpr hbq))⟩

theorem integral_exterior_crt_transfer
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (omega : PrimitiveFrequencyCharacter F) (fS qO : Ideal (𝓞 F))
    (hsplit : FixedSResidue.ConductorSplit A omega.conductor fS qO)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (hinfinite : ∀ w : InfinitePlace F, sigma.1 w = 1)
    (hlocal : ∀ v : {v // v ∈ A.Sf},
      ∃ delta : (v.val.adicCompletion F)ˣ →ₜ* ℂˣ,
        delta.toMonoidHom = sigma.2 v ∧
          IsFrequencyLocalComponent F omega v.val delta)
    (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0)
    (haunit : IsUnit (Ideal.Quotient.mk (FixedSResidue.residueModulus A qO)
      (algebraMap (𝓞 F) A.R a)))
    (hba : b - a ∈ qO) (hbS : b - 1 ∈ fS)
    (hbext : Ideal.span {b} ⊔ A.cS = ⊤)
    (e : A.Exterior)
    (he : Ideal.span {algebraMap (𝓞 F) A.R a} = A.extendIdeal e) :
    omega.character e.val =
      FixedSResidue.localInverseProduct A sigma
        ⟨algebraMap (𝓞 F) A.R a,
          (FaithfulSMul.algebraMap_injective (𝓞 F) A.R).ne ha⟩ *
        omega.character (Ideal.span {b}) := by
  let n : FixedSResidue.NonzeroSInteger A :=
    ⟨algebraMap (𝓞 F) A.R a,
      (FaithfulSMul.algebraMap_injective (𝓞 F) A.R).ne ha⟩
  let x : Fˣ := Units.mk0 (a : F) (by exact_mod_cast ha)
  let y : Fˣ := Units.mk0 (b : F) (by exact_mod_cast hb)
  have hnx : FixedSResidue.fieldUnit A n = x := by
    apply Units.ext
    rfl
  have hs : finiteDiagonalIdele F A (FixedSResidue.fieldUnit A n) =
      ∏ v : {v // v ∈ A.Sf}, IdeleGroup.finitePlaceIdele v.val
        (integralElementLocalUnit F v.val a ha) := by
    rw [hnx]
    unfold finiteDiagonalIdele
    apply Finset.prod_congr rfl
    intro v hv
    congr 1
    apply Units.ext
    rfl
  obtain ⟨hcI, hcJ⟩ := integral_exterior_crt_coprime F A omega.conductor fS qO
    hsplit a b hb haunit hba hbS hbext e he
  have hprime :
      IdeleGroup.principalIdele F (FixedSResidue.fieldUnit A n / y) /
        finiteDiagonalIdele F A (FixedSResidue.fieldUnit A n) ∈
      RayClass.idelePrimeToModulusSubgroup
        (rayClassModulusToOriginal F
          (narrowIdealModulus F omega.conductor omega.conductor_ne_zero)) := by
    rw [hs, hnx]
    exact crt_removed_ratio_mem_primeTo F A omega.conductor fS qO
      omega.conductor_ne_zero hsplit a b ha hb haunit hba hbS
  have hideal :
      IdeleGroup.fractionalIdeal
        (IdeleGroup.principalIdele F (FixedSResidue.fieldUnit A n / y) /
          finiteDiagonalIdele F A (FixedSResidue.fieldUnit A n)) =
        integralUnit F e.val e.property.1 /
          integralUnit F (Ideal.span {b}) (by simpa using hb) := by
    rw [hs, hnx]
    rw [removed_principal_integral_ratio_ideal F x _ b hb]
    rw [s_removed_principal_ideal F A a ha e he]
  exact principal_ratio_transfer F A omega sigma hinfinite hlocal n y
    e.val (Ideal.span {b}) e.property.1 (by simpa using hb) hcI hcJ hprime hideal

end
end DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter.ExteriorCharacterSteps

end
