module

public import DedekindZetaZeroFree.Theta.RayClasses.WeightedIdealBlocks
public import DedekindZetaZeroFree.Arithmetic.Ideals.TraceDualClassInvolution

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke

variable (F : Type) [Field F] [instNF : NumberField F]
variable (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)

include instNF hm

def ramifiedTraceDualClassEquiv : ClassGroup (𝓞 F) ≃ ClassGroup (𝓞 F) where
  toFun C := (principalTraceDualClass F)⁻¹ *
    ClassGroup.mk F (rayIdealFractionalIdeal F m hm) * C⁻¹
  invFun C := (principalTraceDualClass F)⁻¹ *
    ClassGroup.mk F (rayIdealFractionalIdeal F m hm) * C⁻¹
  left_inv := by
    intro C
    simp [mul_inv_rev, mul_comm, mul_left_comm]
  right_inv := by
    intro C
    simp [mul_inv_rev, mul_comm, mul_left_comm]

@[simp] theorem ramifiedTraceDualClassEquiv_apply (C : ClassGroup (𝓞 F)) :
    ramifiedTraceDualClassEquiv F m hm C = (principalTraceDualClass F)⁻¹ *
      ClassGroup.mk F (rayIdealFractionalIdeal F m hm) * C⁻¹ := rfl

@[simp] theorem ramifiedTraceDualClassEquiv_symm_apply (C : ClassGroup (𝓞 F)) :
    (ramifiedTraceDualClassEquiv F m hm).symm C = (principalTraceDualClass F)⁻¹ *
      ClassGroup.mk F (rayIdealFractionalIdeal F m hm) * C⁻¹ := rfl

theorem mk_traceDual_mul_modulus (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    ClassGroup.mk F (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F
      (I * rayIdealFractionalIdeal F m hm)) =
      (ramifiedTraceDualClassEquiv F m hm ((ClassGroup.mk F I)⁻¹))⁻¹ := by
  rw [mk_traceDualIdealUnit, map_mul]
  simp [mul_inv_rev, mul_comm, mul_left_comm]

theorem mk_traceDual_mul_modulus_of_inverse_class
    (C : ClassGroup (𝓞 F)) (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hI : ClassGroup.mk F I = C⁻¹) :
    ClassGroup.mk F (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F
      (I * rayIdealFractionalIdeal F m hm)) =
      (ramifiedTraceDualClassEquiv F m hm C)⁻¹ := by
  rw [mk_traceDual_mul_modulus, hI, inv_inv]

namespace Theta

theorem rayToOrdinary_surjective : Function.Surjective (rayToOrdinary F m hm) := by
  exact ClassFieldTheory.ordinaryRayClassGroupEquivClassGroup.surjective.comp
      (ClassFieldTheory.rayClassIdealModulusProjection_surjective F
        (ClassFieldTheory.ordinaryRayClassModulus_le F (narrowIdealModulus F m hm)))

theorem exists_integral_inverse_ordinaryClass_coprime (C : ClassGroup (𝓞 F)) :
    ∃ a : Ideal (𝓞 F), ∃ ha : a ≠ ⊥,
      a ⊔ m = ⊤ ∧ ClassGroup.mk F (rayIdealFractionalIdeal F a ha) = C⁻¹ := by
  obtain ⟨c, hc⟩ := rayToOrdinary_surjective F m hm C
  obtain ⟨a, ha, hcop, hcls⟩ := exists_integral_inverse_rayIdealClass F m hm c
  refine ⟨a, ha, hcop, ?_⟩
  rw [← rayToOrdinary_rayIdealClass hm a ha hcop c⁻¹ hcls, map_inv, hc]

def inverseOrdinaryClassCoprimeRepresentative (C : ClassGroup (𝓞 F)) :
    (Ideal (𝓞 F))⁰ :=
  ⟨Classical.choose (exists_integral_inverse_ordinaryClass_coprime F m hm C),
    mem_nonZeroDivisors_of_ne_zero
      (Classical.choose (Classical.choose_spec
        (exists_integral_inverse_ordinaryClass_coprime F m hm C)))⟩

theorem inverseOrdinaryClassCoprimeRepresentative_coprime (C : ClassGroup (𝓞 F)) :
    (inverseOrdinaryClassCoprimeRepresentative F m hm C : Ideal (𝓞 F)) ⊔ m = ⊤ := by
  exact (Classical.choose_spec (Classical.choose_spec
      (exists_integral_inverse_ordinaryClass_coprime F m hm C))).1

theorem mk_inverseOrdinaryClassCoprimeRepresentative (C : ClassGroup (𝓞 F)) :
    ClassGroup.mk F
      (FractionalIdeal.mk0 F (inverseOrdinaryClassCoprimeRepresentative F m hm C)) =
      C⁻¹ := by
  exact (Classical.choose_spec (Classical.choose_spec
      (exists_integral_inverse_ordinaryClass_coprime F m hm C))).2

theorem mk_traceDual_mul_modulus_inverseOrdinaryClassCoprimeRepresentative
    (C : ClassGroup (𝓞 F)) :
    ClassGroup.mk F (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F
      (FractionalIdeal.mk0 F (inverseOrdinaryClassCoprimeRepresentative F m hm C) *
        rayIdealFractionalIdeal F m hm)) =
      ClassGroup.mk F (FractionalIdeal.mk0 F
        (inverseOrdinaryClassCoprimeRepresentative F m hm
          (ramifiedTraceDualClassEquiv F m hm C))) := by
  rw [mk_inverseOrdinaryClassCoprimeRepresentative]
  exact mk_traceDual_mul_modulus_of_inverse_class F m hm C _
      (mk_inverseOrdinaryClassCoprimeRepresentative F m hm C)

end Theta
end DedekindZetaZeroFree.Hecke

end
