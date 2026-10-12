module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.CoprimeResidues.UnitOrbitsAndFibers
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterConjugation
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitivePrincipalCharacters

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

private theorem classGroup_rayIdealFractionalIdeal (a : Ideal (𝓞 F)) (ha : a ≠ ⊥) :
    ClassGroup.mk F (rayIdealFractionalIdeal F a ha) =
      ClassGroup.mk0 ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩ := by
  convert ClassGroup.mk_mk0 F ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩ using 1
  congr 1

theorem coprimeIdealResidueRayClass_exists_integral_lift
    (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤)
    (c : RayIdealClass F m hm)
    (hc : rayToOrdinary F m hm c =
      (ClassGroup.mk F (rayIdealFractionalIdeal F a ha))⁻¹) :
    ∃ (x : F) (hx : x ∈ (rayIdealFractionalIdeal F a ha :
        FractionalIdeal (𝓞 F)⁰ F)),
      x ≠ 0 ∧
      integralElementIdeal (rayIdealFractionalIdeal F a ha) ⟨x, hx⟩ ⊔ m = ⊤ ∧
      rayIdealClass F m hm
        (integralElementIdeal (rayIdealFractionalIdeal F a ha) ⟨x, hx⟩) = some c := by
  classical
  obtain ⟨b, hb, hbcop, hbcls⟩ := exists_integral_inverse_rayIdealClass F m hm c⁻¹
  have hbcls : rayIdealClass F m hm b = some c := hbcls.trans (congrArg some (inv_inv c))
  have hbordinary := rayToOrdinary_rayIdealClass hm b hb hbcop c hbcls
  have heq : ClassGroup.mk0 ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩ =
      (ClassGroup.mk0 ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩)⁻¹ := by
    rw [← classGroup_rayIdealFractionalIdeal a ha,
      ← classGroup_rayIdealFractionalIdeal b hb, ← hbordinary, hc, inv_inv]
  obtain ⟨x, hx0, hxab⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp heq
  have hxa : x ∈ a := (Ideal.span_singleton_le_iff_mem a).mp
    (hxab ▸ Ideal.mul_le_left)
  let y : F := algebraMap (𝓞 F) F x
  have hy : y ∈ (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F) :=
    coprimeIdealResidue_mem a ha x hxa
  have hbcoeff : integralElementIdeal (rayIdealFractionalIdeal F a ha) ⟨y, hy⟩ = b := by
    apply FractionalIdeal.coeIdeal_injective (K := F)
    change (integralElementIdeal (rayIdealFractionalIdeal F a ha) ⟨y, hy⟩ : FractionalIdeal (𝓞 F)⁰ F) = (b : FractionalIdeal (𝓞 F)⁰ F)
    rw [integralElementIdeal_integral_coe a ha x hxa hy, ← hxab,
      FractionalIdeal.coeIdeal_mul]
    rw [mul_right_comm, mul_inv_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.mpr ha), one_mul]
  refine ⟨y, hy, ?_, ?_, ?_⟩
  · exact (map_ne_zero_iff (algebraMap (𝓞 F) F) (NumberField.RingOfIntegers.coe_injective)).mpr hx0
  · simpa [hbcoeff] using hbcop
  · simpa [hbcoeff] using hbcls

private theorem integral_lift_isUnit_reduction
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤)
    (x : ↥(rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F))
    (hx : integralElementIdeal (rayIdealFractionalIdeal F a ha) x ⊔ m = ⊤) :
    IsUnit (coprimeIdealResidueReduction F m a hm ha hcop
      (fractionalIdealQuotientMk
        (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
        ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
          FractionalIdeal (𝓞 F)⁰ F) x)) := by
  obtain ⟨z, hz, hzx⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 F)⁰).mp x.property
  have hcoeff : Ideal.span {z} = a * integralElementIdeal (rayIdealFractionalIdeal F a ha) x := by
    apply FractionalIdeal.coeIdeal_injective (K := F)
    change (Ideal.span {z} : FractionalIdeal (𝓞 F)⁰ F) =
      ((a * integralElementIdeal (rayIdealFractionalIdeal F a ha) x : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
    rw [FractionalIdeal.coeIdeal_mul, integralElementIdeal_coe,
      FractionalIdeal.coeIdeal_span_singleton, hzx]
    change FractionalIdeal.spanSingleton (𝓞 F)⁰ x.val =
      (a : FractionalIdeal (𝓞 F)⁰ F) *
        (FractionalIdeal.spanSingleton (𝓞 F)⁰ x.val * (a : FractionalIdeal (𝓞 F)⁰ F)⁻¹)
    rw [mul_left_comm,
      mul_inv_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.mpr ha), mul_one]
  have hp : IsCoprime (Ideal.span {z}) m := by
    rw [hcoeff]
    exact (Ideal.isCoprime_iff_sup_eq.mpr hcop).mul_left
      (Ideal.isCoprime_iff_sup_eq.mpr hx)
  have hxx : x = ⟨(algebraMap (𝓞 F) F) z, coprimeIdealResidue_mem a ha z hz⟩ :=
    Subtype.ext hzx.symm
  rw [hxx, coprimeIdealResidueReduction_mk m a hm ha hcop z hz]
  obtain ⟨i, hi, j, hj, hij⟩ := hp.exists
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp hi
  apply IsUnit.of_mul_eq_one (Ideal.Quotient.mk m k)
  rw [← map_mul, ← map_one (Ideal.Quotient.mk m)]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  have heq : z * k - 1 = -j := by rw [mul_comm, hk, ← hij]; ring
  rw [heq]
  exact m.neg_mem hj

theorem coprimeIdealResidueRayClass_surjective
    (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤) :
    Function.Surjective (coprimeIdealResidueRayClass hF m a hm ha hcop hmt) := by
  classical
  intro c
  obtain ⟨x, hx, hx0, hxcop, hxcls⟩ :=
    coprimeIdealResidueRayClass_exists_integral_lift hF m a hm ha hcop hmt c.val c.property
  let q : coprimeIdealResidueUnits F m a hm ha hcop hmt :=
    ⟨fractionalIdealQuotientMk
      (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
      ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
        FractionalIdeal (𝓞 F)⁰ F) ⟨x, hx⟩,
      integral_lift_isUnit_reduction m a hm ha hcop ⟨x, hx⟩ hxcop⟩
  refine ⟨q, Subtype.ext ?_⟩
  let η := rayCharacterOfGroupCharacter F m hm 1
  have hl := coprimeIdealResidueRayClass_lift hF m a hm ha hcop hmt
    η (chooseRayCharacterData η) q ⟨x, hx⟩ rfl
  exact Option.some.inj (hl.symm.trans hxcls)

theorem coprimeIdealResidueRayClass_fiber_card_all
    (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤)
    (c : {c : RayIdealClass F m hm //
      rayToOrdinary F m hm c =
        (ClassGroup.mk F (rayIdealFractionalIdeal F a ha))⁻¹}) :
    Nat.card {q : coprimeIdealResidueUnits F m a hm ha hcop hmt //
      coprimeIdealResidueRayClass hF m a hm ha hcop hmt q = c} =
        residueUnitImageCard F m := by
  exact (coprimeIdealResidueRayClass_fiber_card hF m a hm ha hcop hmt c
    (coprimeIdealResidueRayClass_surjective hF m a hm ha hcop hmt c)).2

end DedekindZetaZeroFree.Hecke.Theta

end
