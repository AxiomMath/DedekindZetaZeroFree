module

public import DedekindZetaZeroFree.Theta.RayClasses.NormalizedCharacterAggregates
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.OrdinaryClassGroupComparison

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable (F : Type) [Field F] [NumberField F]

 theorem topNarrowModulus_eq_ordinary (hF : NumberField.IsTotallyComplex F)
    (ht : (⊤ : Ideal (𝓞 F)) ≠ ⊥) :
    narrowIdealModulus F ⊤ ht = ClassFieldTheory.ordinaryRayClassModulus F := by
  classical
  apply ClassFieldTheory.RayClassModulus.ext
  · ext v
    rw [narrowIdealModulus_finitePart, ← Ideal.one_eq_top]
    simp only [UniqueFactorizationMonoid.normalizedFactors_one, Multiset.count_zero,
      ClassFieldTheory.ordinaryRayClassModulus, Finsupp.zero_apply]
  · ext v
    exact False.elim ((NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
      (hF.isComplex v.1)) v.2)

 def ordinaryComparison (m : ClassFieldTheory.RayClassModulus F)
    (h : m = ClassFieldTheory.ordinaryRayClassModulus F) :
    ClassFieldTheory.RayClassGroup m ≃* ClassGroup (𝓞 F) := by
  subst m
  exact ClassFieldTheory.ordinaryRayClassGroupEquivClassGroup

private theorem ordinaryComparison_apply (m : ClassFieldTheory.RayClassModulus F)
    (h : m = ClassFieldTheory.ordinaryRayClassModulus F)
    (J : ClassFieldTheory.rayClassPrimeToIdeals m) :
    ordinaryComparison F m h
        (QuotientGroup.mk' (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo m) J) =
      ClassGroup.mk F J.1 := by
  subst m
  apply (ClassGroup.equiv F).injective
  simp only [ordinaryComparison, ClassFieldTheory.ordinaryRayClassGroupEquivClassGroup,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply, ClassGroup.equiv_mk]
  rw [QuotientGroup.congr_mk']
  simp only [FractionalIdeal.canonicalEquiv_self, RingEquiv.coe_mulEquiv_refl]
  rfl

def topRayClassEquivClassGroup (hF : NumberField.IsTotallyComplex F)
    (ht : (⊤ : Ideal (𝓞 F)) ≠ ⊥) :
    RayIdealClass F ⊤ ht ≃* ClassGroup (𝓞 F) :=
  ordinaryComparison F (narrowIdealModulus F ⊤ ht)
    (topNarrowModulus_eq_ordinary F hF ht)

theorem topRayClassEquivClassGroup_rayIdealClass (hF : NumberField.IsTotallyComplex F)
    (ht : (⊤ : Ideal (𝓞 F)) ≠ ⊥)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (c : RayIdealClass F ⊤ ht)
    (hc : rayIdealClass F ⊤ ht I = some c) :
    topRayClassEquivClassGroup F hF ht c =
      ClassGroup.mk F (rayIdealFractionalIdeal F I hI) := by
  have hcoprime : I ⊔ (⊤ : Ideal (𝓞 F)) = ⊤ := sup_top_eq _
  rw [rayIdealClass_eq_some F ⊤ ht I hI hcoprime] at hc
  have heq := Option.some.inj hc
  rw [← heq]
  exact ordinaryComparison_apply F (narrowIdealModulus F ⊤ ht)
    (topNarrowModulus_eq_ordinary F hF ht)
    (rayIdealClassRepresentative F ⊤ ht I hI hcoprime)

theorem topRayClassEquivClassGroup_representatives (hF : NumberField.IsTotallyComplex F)
    (ht : (⊤ : Ideal (𝓞 F)) ≠ ⊥) (D : RayThetaRepresentatives F ⊤ ht)
    (c : RayIdealClass F ⊤ ht) :
    ClassGroup.mk F
      (rayIdealFractionalIdeal F (D.coset c).a (D.coset c).ideal_ne_bot) =
        (topRayClassEquivClassGroup F hF ht c)⁻¹ := by
  rw [← topRayClassEquivClassGroup_rayIdealClass F hF ht (D.coset c).a
    (D.coset c).ideal_ne_bot (c⁻¹) (D.inverse_class c)]
  exact map_inv (topRayClassEquivClassGroup F hF ht) c

end DedekindZetaZeroFree.Hecke.Theta

end
