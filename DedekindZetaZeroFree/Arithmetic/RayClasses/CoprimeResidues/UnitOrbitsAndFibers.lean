module

public import DedekindZetaZeroFree.LFunctions.Hecke.RayResidueIdealCoefficients
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.CosetIdealCorrespondence

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

theorem coprimeIdealResidueRayClass_eq_iff_unit_orbit
    (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤) :
    letI := coprimeIdealResidueUnitAction F m a hm ha hcop hmt
    ∀ q r : coprimeIdealResidueUnits F m a hm ha hcop hmt,
      coprimeIdealResidueRayClass hF m a hm ha hcop hmt q =
        coprimeIdealResidueRayClass hF m a hm ha hcop hmt r ↔
      ∃ ε : residueUnitImage F m, r = ε • q := by
  letI := coprimeIdealResidueUnitAction F m a hm ha hcop hmt
  intro q r
  constructor
  · intro h
    classical
    let η := rayCharacterOfGroupCharacter F m hm 1
    let E := chooseRayCharacterData (hm := hm) η
    let I := rayIdealFractionalIdeal F a ha
    let π := fractionalIdealQuotientMk (I : FractionalIdeal (𝓞 F)⁰ F)
      ((I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F)
    obtain ⟨x, hx⟩ := coprimeIdealResidue_quotientMap_surjective m a hm ha hcop q.val
    obtain ⟨y, hy⟩ := coprimeIdealResidue_quotientMap_surjective m a hm ha hcop r.val
    let X : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)} :=
      ⟨algebraMap (𝓞 F) F x.val, coprimeIdealResidue_mem a ha x.val x.property⟩
    let Y : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)} :=
      ⟨algebraMap (𝓞 F) F y.val, coprimeIdealResidue_mem a ha y.val y.property⟩
    have hxπ : π X = q.val := hx
    have hyπ : π Y = r.val := hy
    have hx0 := coprimeIdealResidueUnits_lift_ne_zero hF m a hm ha hcop hmt η E q X hxπ
    have hy0 := coprimeIdealResidueUnits_lift_ne_zero hF m a hm ha hcop hmt η E r Y hyπ
    have hxN := coprimeIdealResidueUnits_integralElementIdeal_ne_bot hF m a hm ha hcop hmt η E q X hxπ
    have hyN := coprimeIdealResidueUnits_integralElementIdeal_ne_bot hF m a hm ha hcop hmt η E r Y hyπ
    have hxC := coprimeIdealResidueUnits_integralElementIdeal_coprime hF m a hm ha hcop hmt η E q X hxπ
    have hyC := coprimeIdealResidueUnits_integralElementIdeal_coprime hF m a hm ha hcop hmt η E r Y hyπ
    have hclass : rayIdealClass F m hm (integralElementIdeal I X) =
        rayIdealClass F m hm (integralElementIdeal I Y) := by
      rw [coprimeIdealResidueRayClass_lift hF m a hm ha hcop hmt η E q X hxπ,
        coprimeIdealResidueRayClass_lift hF m a hm ha hcop hmt η E r Y hyπ, h]
    rw [rayIdealClass_eq_some F m hm _ hxN hxC,
      rayIdealClass_eq_some F m hm _ hyN hyC] at hclass
    have hp := QuotientGroup.eq.mp (Option.some.inj hclass)
    change (rayIdealFractionalIdeal F (integralElementIdeal I X) hxN)⁻¹ *
      rayIdealFractionalIdeal F (integralElementIdeal I Y) hyN ∈
        ClassFieldTheory.rayPrincipalIdealSubgroup (narrowIdealModulus F m hm) at hp
    obtain ⟨z, hz, hzI⟩ := (ClassFieldTheory.mem_rayPrincipalIdealSubgroup_iff _ _).mp hp
    have hXI : rayIdealFractionalIdeal F (integralElementIdeal I X) hxN =
        toPrincipalIdeal (𝓞 F) F (Units.mk0 X.val hx0) * I⁻¹ := by
      apply Units.ext
      simpa only [Units.val_mul, Units.val_inv_eq_inv_val, coe_toPrincipalIdeal,
        rayIdealFractionalIdeal_coe, Units.val_mk0]
        using integralElementIdeal_coe I X
    have hYI : rayIdealFractionalIdeal F (integralElementIdeal I Y) hyN =
        toPrincipalIdeal (𝓞 F) F (Units.mk0 Y.val hy0) * I⁻¹ := by
      apply Units.ext
      simpa only [Units.val_mul, Units.val_inv_eq_inv_val, coe_toPrincipalIdeal,
        rayIdealFractionalIdeal_coe, Units.val_mk0]
        using integralElementIdeal_coe I Y
    have hspan : FractionalIdeal.spanSingleton (𝓞 F)⁰ (z.val * X.val) =
        FractionalIdeal.spanSingleton (𝓞 F)⁰ Y.val := by
      have he : toPrincipalIdeal (𝓞 F) F (z * Units.mk0 X.val hx0) =
          toPrincipalIdeal (𝓞 F) F (Units.mk0 Y.val hy0) := by
        rw [map_mul, hzI, hXI, hYI]
        simp [mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
      simpa only [coe_toPrincipalIdeal, Units.val_mul, Units.val_mk0] using congrArg Units.val he
    obtain ⟨ε, hε⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
    obtain ⟨b, d, hb0, hd0, hbd, hbm, hdm, _⟩ := positiveRayDenominator F m hm z hz
    have hres : Ideal.Quotient.mk m y.val =
        Ideal.Quotient.mk m (ε : 𝓞 F) * Ideal.Quotient.mk m x.val := by
      have hdy : d * y.val = (ε : 𝓞 F) * (b * x.val) := by
        apply NumberField.RingOfIntegers.coe_injective (K := F)
        push_cast
        change (d : F) * Y.val = (ε : F) * ((b : F) * X.val)
        rw [hbd, ← hε]
        change (d : F) * ((ε : F) * (z.val * X.val)) =
          (ε : F) * (((d : F) * z.val) * X.val)
        ring
      have hb : Ideal.Quotient.mk m b = 1 := by
        simpa only [map_sub, map_one, sub_eq_zero] using
          (Ideal.Quotient.eq_zero_iff_mem.mpr hbm)
      have hd : Ideal.Quotient.mk m d = 1 := by
        simpa only [map_sub, map_one, sub_eq_zero] using
          (Ideal.Quotient.eq_zero_iff_mem.mpr hdm)
      have he := congrArg (Ideal.Quotient.mk m) hdy
      simpa only [map_mul, hd, hb, one_mul] using he
    let εbar : residueUnitImage F m :=
      ⟨Units.map (Ideal.Quotient.mk m).toMonoidHom ε, ⟨ε, rfl⟩⟩
    refine ⟨εbar, ?_⟩
    apply (coprimeIdealResidueUnitsEquiv F m a hm ha hcop hmt).injective
    rw [coprimeIdealResidueUnitAction_apply]
    apply Units.ext
    simp only [Units.val_mul, coprimeIdealResidueUnitsEquiv_coe]
    rw [← hx, ← hy, coprimeIdealResidueReduction_mk, coprimeIdealResidueReduction_mk]
    · exact hres
    · exact x.property
    · exact y.property
  · rintro ⟨ε, rfl⟩
    let η := rayCharacterOfGroupCharacter F m hm 1
    exact (coprimeIdealResidueRayClass_unit_invariant hF m a hm ha hcop hmt
      η (chooseRayCharacterData η) ε q).symm

theorem coprimeIdealResidueRayClass_fiber_card
    (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤)
    (c : {c : RayIdealClass F m hm //
      rayToOrdinary F m hm c =
        (ClassGroup.mk F (rayIdealFractionalIdeal F a ha))⁻¹})
    (hc : c ∈ Set.range (coprimeIdealResidueRayClass hF m a hm ha hcop hmt)) :
    Nonempty {q : coprimeIdealResidueUnits F m a hm ha hcop hmt //
      coprimeIdealResidueRayClass hF m a hm ha hcop hmt q = c} ∧
    Nat.card {q : coprimeIdealResidueUnits F m a hm ha hcop hmt //
      coprimeIdealResidueRayClass hF m a hm ha hcop hmt q = c} =
        residueUnitImageCard F m := by
  classical
  letI := coprimeIdealResidueUnitAction F m a hm ha hcop hmt
  obtain ⟨q, rfl⟩ := hc
  refine ⟨⟨⟨q, rfl⟩⟩, ?_⟩
  let e : {r : coprimeIdealResidueUnits F m a hm ha hcop hmt //
      coprimeIdealResidueRayClass hF m a hm ha hcop hmt r =
        coprimeIdealResidueRayClass hF m a hm ha hcop hmt q} ≃
      MulAction.orbit (residueUnitImage F m) q :=
    Equiv.subtypeEquivRight (fun r => by
      rw [eq_comm, coprimeIdealResidueRayClass_eq_iff_unit_orbit hF m a hm ha hcop hmt]
      exact ⟨fun ⟨ε, hε⟩ => MulAction.mem_orbit_iff.mpr ⟨ε, hε.symm⟩,
        fun h => let ⟨ε, hε⟩ := MulAction.mem_orbit_iff.mp h; ⟨ε, hε.symm⟩⟩)
  exact (Nat.card_congr e).trans
    (coprimeIdealResidueUnitAction_orbit_card m a hm ha hcop hmt q).1

end DedekindZetaZeroFree.Hecke.Theta

end
