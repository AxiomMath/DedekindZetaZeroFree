module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.UnramifiedInertiaCriterion

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField
open IsDedekindDomain

theorem isArithFrobAt_arithmeticFrobeniusRestrictIntermediate
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    (E : IntermediateField K L)
    (p : HeightOneSpectrum (𝓞 K))
    (wE : HeightOneSpectrum (𝓞 ↥E)) (wL : HeightOneSpectrum (𝓞 L))
    (hwE : wE.asIdeal.LiesOver p.asIdeal)
    (hwL : wL.asIdeal.LiesOver wE.asIdeal) :
    IsArithFrobAt (𝓞 K)
      (AlgEquiv.restrictNormalHom ↥E (ClassFieldTheory.arithmeticFrobeniusAt (K := K) wL))
      wE.asIdeal := by
  letI := hwE
  letI := hwL
  haveI : wL.asIdeal.LiesOver p.asIdeal := Ideal.LiesOver.trans wL.asIdeal wE.asIdeal p.asIdeal
  have hL := IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) wL.asIdeal
  intro x
  apply (Ideal.mem_of_liesOver wL.asIdeal wE.asIdeal _).mpr
  rw [map_sub, map_pow]
  have hcomm : algebraMap (𝓞 ↥E) (𝓞 L)
      ((AlgEquiv.restrictNormalHom ↥E (ClassFieldTheory.arithmeticFrobeniusAt (K := K) wL)) • x) =
      ClassFieldTheory.arithmeticFrobeniusAt (K := K) wL • (algebraMap (𝓞 ↥E) (𝓞 L) x) := by
    apply Subtype.ext
    exact AlgEquiv.restrictNormal_commutes (ClassFieldTheory.arithmeticFrobeniusAt (K := K) wL) ↥E (x : ↥E)
  change algebraMap (𝓞 ↥E) (𝓞 L)
      ((AlgEquiv.restrictNormalHom ↥E (ClassFieldTheory.arithmeticFrobeniusAt (K := K) wL)) • x) -
      algebraMap (𝓞 ↥E) (𝓞 L) x ^ Nat.card ((𝓞 K) ⧸ wE.asIdeal.under (𝓞 K)) ∈ wL.asIdeal
  rw [hcomm, ← Ideal.over_def wE.asIdeal p.asIdeal, Ideal.over_def wL.asIdeal p.asIdeal]
  exact hL _

theorem arithmeticFrobeniusRestrictUnramifiedBottom
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    (E : IntermediateField K L)
    (p : HeightOneSpectrum (𝓞 K))
    (wE : HeightOneSpectrum (𝓞 ↥E)) (wL : HeightOneSpectrum (𝓞 L))
    (hwE : wE.asIdeal.LiesOver p.asIdeal)
    (hwL : wL.asIdeal.LiesOver wE.asIdeal)
    (hE : Algebra.IsUnramifiedAt (𝓞 K) wE.asIdeal) :
    AlgEquiv.restrictNormalHom ↥E (ClassFieldTheory.arithmeticFrobeniusAt (K := K) wL) =
      ClassFieldTheory.arithmeticFrobeniusAt (K := K) wE := by
  have hrestrict := isArithFrobAt_arithmeticFrobeniusRestrictIntermediate E p wE wL hwE hwL
  have hchosen : IsArithFrobAt (𝓞 K)
      (ClassFieldTheory.arithmeticFrobeniusAt (K := K) wE) wE.asIdeal :=
    IsArithFrobAt.arithFrobAt (𝓞 K) (↥E ≃ₐ[K] ↥E) wE.asIdeal
  have hratio := hrestrict.mul_inv_mem_inertia hchosen
  rw [(unramifiedIffInertiaBot p wE hwE).mp hE, Subgroup.mem_bot] at hratio
  exact mul_inv_eq_one.mp hratio

end DedekindZetaZeroFree.AbelianQuotient
