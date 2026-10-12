module

public import DedekindZetaZeroFree.ZeroDetection.Conductors.FrequencyLocalComponents

@[expose] public section

open scoped NumberField
open IsDedekindDomain

namespace DedekindZetaZeroFree.Detector.Conductor.LocalTwistSteps

open scoped Classical
open UniqueFactorizationMonoid RayClassBridge
open ClassFieldTheory.GlobalClassFieldComparison

private theorem count_nf (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {I : Ideal (𝓞 F)} (hI : I ≠ 0) :
    FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (Multiset.count v.asIdeal (normalizedFactors I) : ℤ) := by
 rw [FractionalIdeal.count_coe F v hI]
 congr 1
 open Associates in
 rw [factors_mk _ hI, count_some (irreducible_mk.mpr v.irreducible),
    ← Multiset.count_map_eq_count' _ _ Subtype.val_injective, map_subtype_coe_factors',
    factors_eq_normalizedFactors, ← Multiset.count_map_eq_count' _ _ (mk_injective (M := Ideal (𝓞 F)))]
private theorem away_ne_zero (F : Type) [Field F] [NumberField F]
 (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) : Raw.idealAwayPrimePart F v I ≠ 0 := by
 exact prod_ne_zero_of_subset_normalizedFactors (Multiset.filter_subset _ _)
private theorem away_count (F : Type) [Field F] [NumberField F]
 (v w : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) :
 FractionalIdeal.count F w (Raw.idealAwayPrimePart F v I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
   if w = v then 0 else (Multiset.count w.asIdeal (normalizedFactors I) : ℤ) := by
 rw [count_nf F w (away_ne_zero F v I)]
 rw [Raw.idealAwayPrimePart, normalizedFactors_prod_eq_self_of_subset (Multiset.filter_subset _ _)]
 by_cases h : w = v
 · subst w
   simp
 · have h' : w.asIdeal ≠ v.asIdeal := fun he => h (HeightOneSpectrum.ext he)
   simp [h, h']
private theorem away_le_pow (F : Type) [Field F] [NumberField F]
 (v w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v) (I : Ideal (𝓞 F)) (hI : I ≠ 0) :
 Raw.idealAwayPrimePart F v I ≤ w.asIdeal ^ (narrowIdealModulus F I hI).finitePart w := by
 have hdiv : w.asIdeal ^ (narrowIdealModulus F I hI).finitePart w ∣ Raw.idealAwayPrimePart F v I := by
   apply (dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ w.ne_bot) (away_ne_zero F v I)).mpr
   rw [Raw.idealAwayPrimePart, normalizedFactors_prod_eq_self_of_subset (Multiset.filter_subset _ _)]
   rw [normalizedFactors_pow, normalizedFactors_irreducible w.irreducible]
   have he : (narrowIdealModulus F I hI).finitePart w = (normalizedFactors I).count w.asIdeal := by
     rw [narrowIdealModulus_finitePart, count_nf F w hI, Int.toNat_natCast]
   rw [he]
   have h' : w.asIdeal ≠ v.asIdeal := fun he => hw (HeightOneSpectrum.ext he)
   have hrepl (n : ℕ) : n • ({w.asIdeal} : Multiset (Ideal (𝓞 F))) = Multiset.replicate n w.asIdeal := by
     induction n with
     | zero => simp
     | succ n hn => simp [succ_nsmul, hn, Multiset.replicate_succ, ← Multiset.singleton_add, add_comm]
   simpa [h', hrepl] using
     (Multiset.le_count_iff_replicate_le (a := w.asIdeal)
       (s := (normalizedFactors I).filter (fun p => p ≠ v.asIdeal))
       (n := (normalizedFactors I).count w.asIdeal)).mp (by simp [h'])
 exact Ideal.dvd_iff_le.mp hdiv
private theorem away_idele_primeTo (F : Type) [Field F] [NumberField F]
 (hc : NumberField.IsTotallyComplex F) (v : HeightOneSpectrum (𝓞 F))
 (m : Ideal (𝓞 F)) (hm : m ≠ 0) (a : 𝓞 F) (ha : a ≠ 0)
 (hcong : a - 1 ∈ Raw.idealAwayPrimePart F v m) :
 IdeleGroup.principalIdele F (Units.mk0 (a : F) (by exact_mod_cast ha)) /
   IdeleGroup.finitePlaceIdele v (Raw.integralElementLocalUnit F v a ha) ∈
 RayClass.idelePrimeToModulusSubgroup
   (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F (narrowIdealModulus F m hm)) := by
 letI := hc
 constructor
 · change _ ∈ (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F (narrowIdealModulus F m hm)).infiniteCongruenceSubgroup
   rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff]
   intro w hw
   exact False.elim ((NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
     (NumberField.IsTotallyComplex.isComplex w.1)) w.2)
 · intro w hw
   change IdeleGroup.finiteComponent w
     (IdeleGroup.principalIdele F (Units.mk0 (a : F) (by exact_mod_cast ha)) /
       IdeleGroup.finitePlaceIdele v (Raw.integralElementLocalUnit F v a ha)) ∈ _
   rw [map_div]
   change ClassFieldTheory.finitePlaceUnitEmbedding w
     (Units.mk0 (a : F) (by exact_mod_cast ha)) / _ ∈ _
   by_cases h : w = v
   · subst w
     rw [IdeleGroup.finitePlaceIdele_finiteComponent_same]
     have he : ClassFieldTheory.finitePlaceUnitEmbedding v
         (Units.mk0 (a : F) (by exact_mod_cast ha)) = Raw.integralElementLocalUnit F v a ha := by
       apply Units.ext
       rfl
     rw [he]
     simpa only [div_self'] using (RayClass.localHigherUnitGroup v
       ((ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F
          (narrowIdealModulus F m hm)).finitePart v)).one_mem
   · rw [IdeleGroup.finitePlaceIdele_finiteComponent_of_ne v w _ h, div_one]
     apply (integral_mem_rayLocalHigherUnitGroup_iff F w _
       (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hw)) a ha _ rfl).mpr
     exact away_le_pow F v w h m hm hcong
private theorem away_idele_ideal (F : Type) [Field F] [NumberField F]
 (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) (ha : a ≠ 0) :
 IdeleGroup.fractionalIdeal
   (IdeleGroup.principalIdele F (Units.mk0 (a : F) (by exact_mod_cast ha)) /
     IdeleGroup.finitePlaceIdele v (Raw.integralElementLocalUnit F v a ha)) =
 integralUnit F (Raw.idealAwayPrimePart F v (Ideal.span {a}))
   (away_ne_zero F v _) := by
 have he (w : HeightOneSpectrum (𝓞 F)) : ClassFieldTheory.finitePlaceUnitEmbedding w
     (Units.mk0 (a : F) (by exact_mod_cast ha)) = Raw.integralElementLocalUnit F w a ha := by
   apply Units.ext
   rfl
 have hp : IdeleGroup.fractionalIdeal
     (IdeleGroup.principalIdele F (Units.mk0 (a : F) (by exact_mod_cast ha))) =
     integralUnit F (Ideal.span {a}) (by simpa using ha) := by
   rw [IdeleGroup.fractionalIdeal_principalIdele]
   apply Units.ext
   rw [coe_toPrincipalIdeal]
   change FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F) =
     (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
   rw [FractionalIdeal.coeIdeal_span_singleton]
 have hc (z : IdeleGroup F) (w : HeightOneSpectrum (𝓞 F)) :
     FractionalIdeal.count F w
       (IdeleGroup.fractionalIdeal z : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
       (FiniteIdeleGroup.localOrder w (IdeleGroup.finiteComponent w z)).toAdd := by
   change FractionalIdeal.count F w
     (((FractionalIdealGroup.factorization (K := F)) (FiniteIdeleGroup.valuationVector z.2) :
       FractionalIdealGroup F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = _
   rw [FractionalIdealGroup.count_factorization, FiniteIdeleGroup.valuationVector_apply]
   rfl
 apply FractionalIdealGroup.ext_count
 intro w
 rw [hc]
 change _ = FractionalIdeal.count F w
   (Raw.idealAwayPrimePart F v (Ideal.span {a}) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
 rw [away_count]
 rw [map_div]
 by_cases hw : w = v
 · subst w
   rw [IdeleGroup.finitePlaceIdele_finiteComponent_same]
   change (FiniteIdeleGroup.localOrder v (ClassFieldTheory.finitePlaceUnitEmbedding v
     (Units.mk0 (a : F) (by exact_mod_cast ha)) / Raw.integralElementLocalUnit F v a ha)).toAdd = _
   rw [he, div_self', map_one]
   simp
 · rw [IdeleGroup.finitePlaceIdele_finiteComponent_of_ne v w _ hw, div_one]
   rw [if_neg hw, ← count_nf F w (show (Ideal.span {a} : Ideal (𝓞 F)) ≠ 0 by simpa using ha)]
   rw [← hc, hp]
   rfl

private theorem primeTo_idele_evaluation (F : Type) [Field F] [NumberField F] (hc : NumberField.IsTotallyComplex F)
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

theorem idelic_restriction_is_raw_local_component
    (F : Type) [Field F] [NumberField F] (hc : NumberField.IsTotallyComplex F)
    (χ : PrimitiveFrequencyCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (δ : (v.adicCompletion F)ˣ →ₜ* ℂˣ)
    (hδ : ∀ u : (v.adicCompletion F)ˣ,
      δ u = RayClassBridge.ideleClassCharacter F hc
        χ.conductor χ.conductor_ne_zero χ.character
        (IdeleGroup.finitePlaceIdeleClass v u)) :
    Raw.IsFrequencyLocalComponent F χ v δ := by
  classical
  intro a ha hcong
  let x : Fˣ := Units.mk0 (a : F) (by exact_mod_cast ha)
  let u := Raw.integralElementLocalUnit F v a ha
  let z := IdeleGroup.principalIdele F x / IdeleGroup.finitePlaceIdele v u
  let I := Raw.idealAwayPrimePart F v (Ideal.span {a})
  have hz := away_idele_primeTo F hc v χ.conductor χ.conductor_ne_zero a ha hcong
  have hid := away_idele_ideal F v a ha
  have hI : I ≠ ⊥ := away_ne_zero F v _
  have hcop : I ⊔ χ.conductor = ⊤ := by
    apply (integralUnit_mem_primeTo_iff F χ.conductor χ.conductor_ne_zero I hI).mp
    have hh := RayClass.fractionalIdeal_mem_primeToModulusIdeals _ z hz
    rw [hid] at hh
    exact hh
  have heval := primeTo_idele_evaluation F hc χ.conductor χ.conductor_ne_zero χ.character z hz
  have heq : (⟨IdeleGroup.fractionalIdeal z,
      RayClass.fractionalIdeal_mem_primeToModulusIdeals _ z hz⟩ :
      ClassFieldTheory.rayClassPrimeToIdeals
        (narrowIdealModulus F χ.conductor χ.conductor_ne_zero)) =
      integralPrimeTo F χ.conductor χ.conductor_ne_zero I hI hcop := by
    apply Subtype.ext
    exact hid
  rw [heq] at heval
  have hprin : QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
      (IdeleGroup.principalIdele F x) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨x, rfl⟩
  have hzclass : QuotientGroup.mk' (IdeleGroup.principalSubgroup F) z =
      (IdeleGroup.finitePlaceIdeleClass v u)⁻¹ := by
    change QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
      (IdeleGroup.principalIdele F x / IdeleGroup.finitePlaceIdele v u) = _
    rw [map_div, hprin, one_div]
    rfl
  rw [hzclass, map_inv] at heval
  have hcval := congrArg (fun y : ℂˣ => (y : ℂ)) heval
  rw [fractionalCharacter_integral] at hcval
  change (δ u : ℂ) = (χ.character I)⁻¹
  rw [hδ]
  rw [Units.val_inv_eq_inv_val] at hcval
  exact inv_eq_iff_eq_inv.mp hcval

end DedekindZetaZeroFree.Detector.Conductor.LocalTwistSteps
