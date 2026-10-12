module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.IntegralCharacters

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

def frozenPrincipalRayClass (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (α : 𝓞 F) (hα : α ≠ 0) (hcop : Ideal.span ({α} : Set (𝓞 F)) ⊔ m = ⊤) :
    ClassFieldTheory.RayClassGroup (M F m hm) :=
  frozenIntegralRayClass F m hm (Ideal.span {α})
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hα) hcop

def frozenFinitePlaceRayClass (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* ClassFieldTheory.RayClassGroup (M F m hm) :=
  (ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele
      F (M F m hm)).symm.toMonoidHom.comp
    ((QuotientGroup.mk'
      (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal
        F (M F m hm)).congruenceSubgroup).comp
      (IdeleGroup.finitePlaceIdeleClass v))

def frozenPrincipalLocalUnit (F : Type) [Field F] [NumberField F]
    (α : 𝓞 F) (hα : α ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ :=
  Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom
    (Units.mk0 (α : F) (by exact_mod_cast hα))

private theorem principalRay_count_idele (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : IdeleGroup F) :
    FractionalIdeal.count F v (IdeleGroup.fractionalIdeal a :
      FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (FiniteIdeleGroup.localOrder v (a.2 v)).toAdd := by
  exact (FractionalIdealGroup.count_factorization _ v).trans
    (FiniteIdeleGroup.valuationVector_apply _ _)

private theorem principalRay_single_ideal (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ)
    (hx : (FiniteIdeleGroup.localOrder v x).toAdd = 0) :
    IdeleGroup.fractionalIdeal (IdeleGroup.finitePlaceIdele v x) = 1 := by
  apply FractionalIdealGroup.ext_count
  intro w
  rw [principalRay_count_idele, Units.val_one, FractionalIdeal.count_one]
  change (FiniteIdeleGroup.localOrder w
    (IdeleGroup.finiteComponent w (IdeleGroup.finitePlaceIdele v x))).toAdd = 0
  by_cases hw : w = v
  · subst w
    rwa [IdeleGroup.finitePlaceIdele_finiteComponent_same]
  · rw [IdeleGroup.finitePlaceIdele_finiteComponent_of_ne v w x hw]
    simp

private theorem principalRay_product_component (F : Type) [Field F] [NumberField F]
    (s : Finset (HeightOneSpectrum (𝓞 F)))
    (f : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (w : HeightOneSpectrum (𝓞 F)) :
    IdeleGroup.finiteComponent w (∏ v ∈ s, IdeleGroup.finitePlaceIdele v (f v)) =
      if w ∈ s then f w else 1 := by
  classical
  rw [map_prod]
  by_cases hw : w ∈ s
  · rw [if_pos hw]
    rw [Finset.prod_eq_single_of_mem w hw]
    · exact IdeleGroup.finitePlaceIdele_finiteComponent_same w (f w)
    · intro v _ hv
      exact IdeleGroup.finitePlaceIdele_finiteComponent_of_ne v w (f v) hv.symm
  · rw [if_neg hw]
    apply Finset.prod_eq_one
    intro v hv
    exact IdeleGroup.finitePlaceIdele_finiteComponent_of_ne v w (f v)
      (fun h => hw (h.symm ▸ hv))

theorem rm_kummer_ray_principal_relation (F : Type) [Field F] [NumberField F]
    (htc : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (α : 𝓞 F) (hα : α ≠ 0) (hcop : Ideal.span ({α} : Set (𝓞 F)) ⊔ m = ⊤) :
    frozenPrincipalRayClass F m hm α hα hcop =
      ∏ v ∈ (M F m hm).finitePart.support,
        (frozenFinitePlaceRayClass F m hm v (frozenPrincipalLocalUnit F α hα v))⁻¹ := by
  let x : Fˣ := Units.mk0 (α : F) (by exact_mod_cast hα)
  let p := IdeleGroup.principalIdele F x
  let s := (M F m hm).finitePart.support
  let b : IdeleGroup F := ∏ v ∈ s,
    IdeleGroup.finitePlaceIdele v (frozenPrincipalLocalUnit F α hα v)
  let a := p * b⁻¹
  let m' := ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal
    F (M F m hm)
  have hp : IdeleGroup.fractionalIdeal p =
      RayClassBridge.integralUnit F (Ideal.span {α})
        (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hα) := by
    rw [IdeleGroup.fractionalIdeal_principalIdele]
    apply Units.ext
    rw [coe_toPrincipalIdeal, RayClassBridge.integralUnit_val,
      FractionalIdeal.coeIdeal_span_singleton]
    rfl
  have hpv (v : HeightOneSpectrum (𝓞 F)) :
      IdeleGroup.finiteComponent v p = frozenPrincipalLocalUnit F α hα v := by
    apply Units.ext
    rfl
  have hv (v : HeightOneSpectrum (𝓞 F)) (hvs : v ∈ s) :
      (FiniteIdeleGroup.localOrder v (frozenPrincipalLocalUnit F α hα v)).toAdd = 0 := by
    rw [← hpv]
    change (FiniteIdeleGroup.localOrder v (p.2 v)).toAdd = 0
    rw [← principalRay_count_idele, hp]
    exact (frozenIntegralPrimeTo F m hm (Ideal.span {α})
      (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hα) hcop).property v hvs
  have hb : IdeleGroup.fractionalIdeal b = 1 := by
    dsimp [b]
    rw [map_prod]
    apply Finset.prod_eq_one
    intro v hvs
    exact principalRay_single_ideal F v _ (hv v hvs)
  have ha : a ∈ RayClass.idelePrimeToModulusSubgroup m' := by
    constructor
    · change a.1 ∈ m'.infiniteCongruenceSubgroup
      rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff]
      intro v hvm
      exact (Finset.notMem_empty v hvm).elim
    · intro v hvs
      change IdeleGroup.finiteComponent v a ∈ RayClass.localHigherUnitGroup v (m'.finitePart v)
      have hc := principalRay_product_component F s
        (frozenPrincipalLocalUnit F α hα) v
      change v ∈ s at hvs
      rw [if_pos hvs] at hc
      change IdeleGroup.finiteComponent v b = _ at hc
      change IdeleGroup.finiteComponent v (p * b⁻¹) ∈ _
      rw [map_mul, map_inv, hpv, hc, mul_inv_cancel]
      exact (RayClass.localHigherUnitGroup v (m'.finitePart v)).one_mem
  have hai : IdeleGroup.fractionalIdeal a = IdeleGroup.fractionalIdeal p := by
    dsimp [a]
    rw [map_mul, map_inv, hb, inv_one, mul_one]
  let Q : IdeleGroup F →* RayClass.RayClassGroup m' :=
    (QuotientGroup.mk' m'.congruenceSubgroup).comp
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup F))
  let E := ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele
    F (M F m hm)
  letI : CommGroup (RayClass.RayClassGroup m') :=
    { toGroup := inferInstance
      mul_comm := fun a b => E.symm.injective (by
        rw [map_mul, map_mul]
        exact mul_comm (E.symm a) (E.symm b)) }
  have hEa : E (frozenPrincipalRayClass F m hm α hα hcop) = Q a := by
    apply (RayClass.rayClassGroupEquivIdealRayClassGroup m').injective
    have hproj := GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo
      m' ⟨a, ha⟩
    change (RayClass.rayClassGroupEquivIdealRayClassGroup m') (Q a) = _ at hproj
    rw [hproj]
    change (RayClass.rayClassGroupEquivIdealRayClassGroup m')
      ((RayClass.rayClassGroupEquivIdealRayClassGroup m').symm
        (ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginal F (M F m hm)
          (frozenPrincipalRayClass F m hm α hα hcop))) = _
    rw [MulEquiv.apply_symm_apply]
    have ht : RayClass.primeToIdealMap m' ⟨a, ha⟩ =
        frozenIntegralPrimeTo F m hm (Ideal.span {α})
          (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hα) hcop := by
      apply Subtype.ext
      exact hai.trans hp
    rw [RayClass.idealRayProjection, MonoidHom.comp_apply, ht]
    rfl
  have hQp : Q p = 1 := by
    have hp' : p ∈ IdeleGroup.principalSubgroup F := ⟨x, rfl⟩
    dsimp [Q]
    rw [(QuotientGroup.eq_one_iff p).mpr hp']
    exact map_one (QuotientGroup.mk' m'.congruenceSubgroup)
  apply E.injective
  rw [hEa]
  dsimp [a]
  rw [map_mul, hQp, one_mul, map_inv]
  dsimp [b]
  rw [map_prod, ← Finset.prod_inv_distrib, map_prod]
  apply Finset.prod_congr rfl
  intro v hvs
  rw [map_inv]
  congr 1
  change _ = E (E.symm (Q (IdeleGroup.finitePlaceIdele v
    (frozenPrincipalLocalUnit F α hα v))))
  exact (E.apply_symm_apply _).symm

end
end DedekindZetaZeroFree
