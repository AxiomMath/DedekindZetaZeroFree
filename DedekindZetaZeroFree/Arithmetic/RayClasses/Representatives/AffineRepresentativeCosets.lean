module

public import DedekindZetaZeroFree.LFunctions.Hecke.RayResidueIdealCoefficients
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.CosetIdealCorrespondence

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

theorem exists_rayRepresentative_affine_multiplier
    (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤)
    (D : RayThetaRepresentatives F m hm)
    (q : coprimeIdealResidueUnits F m a hm ha hcop hmt)
    (x : {x : F // x ∈
      (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)})
    (hx : fractionalIdealQuotientMk
      (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
      ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
        FractionalIdeal (𝓞 F)⁰ F) x = q.val) :
    let c := (coprimeIdealResidueRayClass hF m a hm ha hcop hmt q).val
    ∃ (γ : Fˣ) (y : 𝓞 F),
      (rayIdealFractionalIdeal F (D.coset c).a (D.coset c).ideal_ne_bot :
        FractionalIdeal (𝓞 F)⁰ F) =
        FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
          (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F) ∧
      (algebraMap (𝓞 F) F) y = (γ : F) * x.val ∧
      y ∈ (D.coset c).a ∧ y - 1 ∈ m ∧
      y - (D.coset c).b ∈ (D.coset c).a * m := by
  classical
  dsimp only
  let c := (coprimeIdealResidueRayClass hF m a hm ha hcop hmt q).val
  let A := (D.coset c).a
  let B := integralElementIdeal (rayIdealFractionalIdeal F a ha) x
  let η := rayCharacterOfGroupCharacter F m hm (1 : RayIdealClass F m hm →* ℂˣ)
  let E := chooseRayCharacterData (hm := hm) η
  have hx0 : x.val ≠ 0 := coprimeIdealResidueUnits_lift_ne_zero hF m a hm ha hcop hmt η E q x hx
  have hBc : rayIdealClass F m hm B = some c :=
    coprimeIdealResidueRayClass_lift hF m a hm ha hcop hmt η E q x hx
  have hAc : rayIdealClass F m hm A = some c⁻¹ := D.inverse_class c
  have hBA : rayIdealClass F m hm (B * A) = some 1 := by
    rw [rayIdealClass_mul, hBc, hAc]
    simp
  have hn : B * A ≠ ⊥ := by
    intro h
    have hh := rayIdealClass_eq_none F m hm (B * A) (Or.inl h)
    rw [hBA] at hh
    contradiction
  have hBAcop : B * A ⊔ m = ⊤ := by
    by_contra h
    have hh := rayIdealClass_eq_none F m hm (B * A) (Or.inr h)
    rw [hBA] at hh
    contradiction
  rw [rayIdealClass_eq_some F m hm (B * A) hn hBAcop] at hBA
  have hp := (QuotientGroup.eq_one_iff _).mp (Option.some.inj hBA)
  change rayIdealFractionalIdeal F (B * A) hn ∈
    ClassFieldTheory.rayPrincipalIdealSubgroup (narrowIdealModulus F m hm) at hp
  obtain ⟨u, hu, huI⟩ := (ClassFieldTheory.mem_rayPrincipalIdealSubgroup_iff _ _).mp hp
  have he : FractionalIdeal.spanSingleton (𝓞 F)⁰ (u : F) =
      ((B * A : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) := by
    simpa [coe_toPrincipalIdeal] using congrArg Units.val huI
  have hum : (u : F) ∈ ((B * A : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [← he]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨y, hy, hyu⟩ := (FractionalIdeal.mem_coeIdeal _).mp hum
  change (algebraMap (𝓞 F) F) y = (u : F) at hyu
  have hy0 : (y : F) ≠ 0 := by
    change (algebraMap (𝓞 F) F) y ≠ 0
    rw [hyu]
    exact u.ne_zero
  have hyunit : Units.mk0 (y : F) hy0 = u := by
    apply Units.ext
    exact hyu
  have hyray := (integralNarrowRayCongruence F m hm y hy0).mp (hyunit ▸ hu)
  let γ : Fˣ := u / Units.mk0 x.val hx0
  have hγx : (γ : F) * x.val = (u : F) := by
    simp [γ, div_eq_mul_inv, mul_assoc, hx0]
  have hA : (rayIdealFractionalIdeal F A (D.coset c).ideal_ne_bot :
      FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F) := by
    have he' := he
    rw [FractionalIdeal.coeIdeal_mul, integralElementIdeal_coe] at he'
    have hγspan : FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) =
        FractionalIdeal.spanSingleton (𝓞 F)⁰ (u : F) *
          (FractionalIdeal.spanSingleton (𝓞 F)⁰ x.val)⁻¹ := by
      simp [γ, div_eq_mul_inv, FractionalIdeal.spanSingleton_inv,
        FractionalIdeal.spanSingleton_mul_spanSingleton]
    rw [hγspan, he', rayIdealFractionalIdeal_coe]
    have hi : (a : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr ha
    have hxs : FractionalIdeal.spanSingleton (𝓞 F)⁰ x.val ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx0
    field_simp
    simp [rayIdealFractionalIdeal_coe, hi]
  refine ⟨γ, y, hA, hyu.trans hγx.symm, Ideal.mul_le_right hy, hyray.1, ?_⟩
  have hyC : y ∈ RayCoset.C (D.coset c) :=
    (RayCoset.mem_C_iff (D.coset c) y).mpr
      ⟨Ideal.mul_le_right hy, (D.modulus_eq c).symm ▸ hyray.1⟩
  change y - (D.coset c).b ∈ (D.coset c).a * (D.coset c).m at hyC
  simpa only [D.modulus_eq c] using hyC

end DedekindZetaZeroFree.Hecke.Theta

end
