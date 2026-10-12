module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.PrincipalLocalUnitRelation
public import DedekindZetaZeroFree.Arithmetic.Kummer.LeastLocalConductorExponent

@[expose] public section

namespace DedekindZetaZeroFree.RMKummerPrincipalPrime

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

theorem principal_product (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (α : 𝓞 F) (hα : α ≠ 0)
    (hcop : Ideal.span ({α} : Set (𝓞 F)) ⊔ RMKummerConductor.m F h12 x = ⊤) :
    RMKummerConductor.Xi F h12 x (Ideal.span {α}) =
      ∏ v ∈ (M F (RMKummerConductor.m F h12 x)
        (RMKummerConductor.m_ne_bot F h12 x)).finitePart.support,
        (RMKummerLocalNormCharacter.lambda F h12 x v
          (frozenPrincipalLocalUnit F α hα v) : ℂ)⁻¹ := by
  change frozenRayValue F _ _ _ _ = _
  rw [frozenRayValue_of_primeTo F _ _ _ _
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hα) hcop]
  change (RMKummerConductor.rho F h12 x
    (frozenPrincipalRayClass F _ _ α hα hcop) : ℂ) = _
  rw [rm_kummer_ray_principal_relation F (RMKummerConductor.totallyComplex F h12)]
  rw [map_prod, Units.coe_prod]
  apply Finset.prod_congr rfl
  intro v hv
  have heq := RMKummerLocalNormCharacter.rho_localToRay F h12 x v
    (frozenPrincipalLocalUnit F α hα v)
  change RMKummerConductor.rho F h12 x
      (frozenFinitePlaceRayClass F _ _ v (frozenPrincipalLocalUnit F α hα v)) =
    RMKummerLocalNormCharacter.lambda F h12 x v
      (frozenPrincipalLocalUnit F α hα v) at heq
  simpa only [map_inv, Units.val_inv_eq_inv_val] using congrArg Units.val (congrArg Inv.inv heq)

theorem prime_arithmeticFrobenius (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (M F (RMKummerConductor.m F h12 x)
      (RMKummerConductor.m_ne_bot F h12 x)).finitePart.support)
    (w : HeightOneSpectrum (𝓞 (RMKummerConductor.E F h12 x)))
    (hw : w.asIdeal.LiesOver v.asIdeal) :
    RMKummerConductor.Xi F h12 x v.asIdeal =
      (RMKummerConductor.kappa F h12 x
        (ClassFieldTheory.arithmeticFrobeniusAt (K := F) w) : ℂ) := by
  have hcop : v.asIdeal ⊔ RMKummerConductor.m F h12 x = ⊤ := by
    apply (RayClassBridge.integralUnit_mem_primeTo_iff F _
      (RMKummerConductor.m_ne_bot F h12 x) _ v.ne_bot).mp
    intro q hq
    exact FractionalIdeal.count_maximal_coprime F q
      (fun h => hv (h ▸ hq))
  change frozenRayValue F _ _ _ _ = _
  rw [frozenRayValue_of_primeTo F _ _ _ _ v.ne_bot hcop]
  exact congrArg Units.val (RMKummerConductor.rho_prime F h12 x v hv w hw)

private theorem lambda_eq_of_order_one
    (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (M F (RMKummerConductor.m F h12 x)
      (RMKummerConductor.m_ne_bot F h12 x)).finitePart.support)
    (π π' : (v.adicCompletion F)ˣ)
    (hπ : (FiniteIdeleGroup.localOrder v π).toAdd = 1)
    (hπ' : (FiniteIdeleGroup.localOrder v π').toAdd = 1) :
    RMKummerLocalNormCharacter.lambda F h12 x v π =
      RMKummerLocalNormCharacter.lambda F h12 x v π' := by
  have he : idealPrimeExponent v.asIdeal (RMKummerConductor.m F h12 x) = 0 := by
    simpa only [M_finitePart] using Finsupp.notMem_support_iff.mp hv
  have hu : π / π' ∈ (v.adicCompletionIntegers F).units := by
    apply (FiniteIdeleGroup.localOrder_eq_zero_iff v _).mp
    rw [map_div]
    change (FiniteIdeleGroup.localOrder v π).toAdd -
      (FiniteIdeleGroup.localOrder v π').toAdd = 0
    rw [hπ, hπ', sub_self]
  have hl := RMKummerLeastLocalExponent.lambda_trivial_on_conductor_units
    F h12 x v (π / π') (by
      rw [he, RMKummerLeastLocalExponent.higherUnitGroup_zero F v]
      exact hu)
  rw [map_div] at hl
  exact eq_of_div_eq_one hl

private theorem localOrder_of_uniformizer
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (π : (v.adicCompletion F)ˣ)
    (hπ : HeightOneSpectrum.adicCompletion.valuation F v (π : v.adicCompletion F) =
      WithZero.exp (-1 : ℤ)) :
    (FiniteIdeleGroup.localOrder v π).toAdd = 1 := by
  rw [FiniteIdeleGroup.localOrder_apply]
  change -WithZero.log (HeightOneSpectrum.adicCompletion.valuation F v
    (π : v.adicCompletion F)) = 1
  rw [hπ, WithZero.log_exp]
  rfl

theorem arithmeticFrobenius_eq_lambda_uniformizer
    (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (M F (RMKummerConductor.m F h12 x)
      (RMKummerConductor.m_ne_bot F h12 x)).finitePart.support)
    (w : HeightOneSpectrum (𝓞 (RMKummerConductor.E F h12 x)))
    (hw : w.asIdeal.LiesOver v.asIdeal)
    (π : (v.adicCompletion F)ˣ)
    (hπ : HeightOneSpectrum.adicCompletion.valuation F v (π : v.adicCompletion F) =
      WithZero.exp (-1 : ℤ)) :
    RMKummerConductor.kappa F h12 x
        (ClassFieldTheory.arithmeticFrobeniusAt (K := F) w) =
      RMKummerLocalNormCharacter.lambda F h12 x v π := by
  let m := M F (RMKummerConductor.m F h12 x)
    (RMKummerConductor.m_ne_bot F h12 x)
  let e := ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele F m
  have hr : RMKummerLocalNormCharacter.localToRay F h12 x v
      (FiniteIdeleGroup.chosenLocalOrderSection v 1) =
      ClassFieldTheory.rayClassOfFinitePrime m v hv := by
    apply e.injective
    change e (e.symm _) = _
    rw [e.apply_symm_apply]
    exact (ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime
      F m v hv).symm
  rw [← RMKummerConductor.rho_prime F h12 x v hv w hw, ← hr,
    RMKummerLocalNormCharacter.rho_localToRay]
  exact lambda_eq_of_order_one F h12 x v hv _ π
    (FiniteIdeleGroup.localOrder_chosenLocalOrderSection v 1)
    (localOrder_of_uniformizer F v π hπ)

end
end DedekindZetaZeroFree.RMKummerPrincipalPrime
