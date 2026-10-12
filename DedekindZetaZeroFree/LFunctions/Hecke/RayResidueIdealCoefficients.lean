module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.CoprimeResidues.ReductionAndUnitAction
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterOfGroupCharacter

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

namespace ResidueCoefficientAux

theorem integral_lift (a : Ideal (𝓞 F)) (ha : a ≠ ⊥)
    (x : {x : F // x ∈ (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)}) :
    ∃ α : 𝓞 F, α ∈ a ∧ (algebraMap (𝓞 F) F) α = x.val := by
  exact (FractionalIdeal.mem_coeIdeal (𝓞 F)⁰).mp x.property

theorem coefficient_mul (a : Ideal (𝓞 F)) (ha : a ≠ ⊥)
    (x : {x : F // x ∈ (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)})
    (α : 𝓞 F) (hαx : (algebraMap (𝓞 F) F) α = x.val) :
    integralElementIdeal (rayIdealFractionalIdeal F a ha) x * a = Ideal.span {α} := by
  apply FractionalIdeal.coeIdeal_injective (K := F)
  change ((integralElementIdeal (rayIdealFractionalIdeal F a ha) x * a : Ideal (𝓞 F)) :
    FractionalIdeal (𝓞 F)⁰ F) = (Ideal.span {α} : FractionalIdeal (𝓞 F)⁰ F)
  rw [FractionalIdeal.coeIdeal_mul, integralElementIdeal_coe, ← hαx,
    ← FractionalIdeal.coeIdeal_span_singleton]
  change ((Ideal.span {α} : FractionalIdeal (𝓞 F)⁰ F) *
    (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)⁻¹) *
      rayIdealFractionalIdeal F a ha = _
  rw [mul_assoc, ← Units.val_inv_eq_inv_val, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, mul_one]

theorem quotient_unit_iff (m : Ideal (𝓞 F)) (α : 𝓞 F) :
    IsUnit (Ideal.Quotient.mk m α) ↔ Ideal.span {α} ⊔ m = ⊤ := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (↑(u⁻¹) : 𝓞 F ⧸ m)
    have hab : α * β - 1 ∈ m := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, map_mul, map_one, ← hu, hβ]
      simp
    apply (Ideal.eq_top_iff_one _).mpr
    have hαβ : α * β ∈ Ideal.span {α} ⊔ m :=
      Ideal.mem_sup_left (Ideal.mul_mem_right β _ (Ideal.subset_span (by simp)))
    have hd : α * β - 1 ∈ Ideal.span {α} ⊔ m := Ideal.mem_sup_right hab
    simpa using (Ideal.span {α} ⊔ m).sub_mem hαβ hd
  · intro h
    obtain ⟨β, γ, hγ, heq⟩ := Ideal.mem_span_singleton_sup.mp
      (show (1 : 𝓞 F) ∈ Ideal.span {α} ⊔ m by rw [h]; trivial)
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk m β, ?_⟩
    have ht := congrArg (Ideal.Quotient.mk m) heq
    rw [map_add, map_mul, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr hγ,
      add_zero] at ht
    simpa [mul_comm] using ht

end ResidueCoefficientAux
private theorem span_coprime_of_unit (m : Ideal (𝓞 F)) (α : 𝓞 F)
    (hu : IsUnit (Ideal.Quotient.mk m α)) : Ideal.span {α} ⊔ m = ⊤ := by
  obtain ⟨z, hz⟩ := hu.exists_right_inv
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hc : α * z - 1 ∈ m := Ideal.Quotient.eq.mp (by simpa using hz)
  apply (Ideal.eq_top_iff_one _).mpr
  have h1 : α * z ∈ Ideal.span {α} ⊔ m :=
    Ideal.mem_sup_left (Ideal.mul_mem_right z _ (Ideal.subset_span (by simp)))
  have h2 := (Ideal.span {α} ⊔ m).sub_mem h1 (Ideal.mem_sup_right hc)
  simpa using h2
private theorem positive_empty (hF : NumberField.IsTotallyComplex F) (x : F) :
    ∀ φ : F →+* ℝ, 0 < φ x := by
  letI := hF
  intro φ
  exfalso
  apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal
    (Complex.ofRealHom.comp φ)
  ext y
  simp
private theorem principal_ray_compatible (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (α β : 𝓞 F) (hu : IsUnit (Ideal.Quotient.mk m α))
    (hres : Ideal.Quotient.mk m α = Ideal.Quotient.mk m β) :
    rayIdealClass F m hm (Ideal.span {α}) = rayIdealClass F m hm (Ideal.span {β}) := by
  obtain ⟨z, hz⟩ := hu.exists_right_inv
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hzα : Ideal.Quotient.mk m (α * z) = 1 := by simpa using hz
  have hzβ : Ideal.Quotient.mk m (β * z) = 1 := by simpa [← hres] using hz
  have hαz : α * z ≠ 0 := by
    intro he
    have : (1 : 𝓞 F ⧸ m) = 0 := by simpa [he] using hzα.symm
    exact hmt (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using this) |> (Ideal.eq_top_iff_one _).mpr)
  have hβz : β * z ≠ 0 := by
    intro he
    have : (1 : 𝓞 F ⧸ m) = 0 := by simpa [he] using hzβ.symm
    exact hmt (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using this) |> (Ideal.eq_top_iff_one _).mpr)
  have hzc : Ideal.span {z} ⊔ m = ⊤ := span_coprime_of_unit m z
    (⟨⟨Ideal.Quotient.mk m z, Ideal.Quotient.mk m α, by simpa [mul_comm] using hz, hz⟩, rfl⟩)
  have hzn : Ideal.span {z} ≠ ⊥ := by
    intro he
    exact hαz (by simp [Ideal.span_singleton_eq_bot.mp he])
  have hA := rayIdealClass_span F m hm (α*z) hαz (Ideal.Quotient.eq.mp (by simpa using hzα)) (positive_empty hF _)
  have hB := rayIdealClass_span F m hm (β*z) hβz (Ideal.Quotient.eq.mp (by simpa using hzβ)) (positive_empty hF _)
  rw [← Ideal.span_singleton_mul_span_singleton, rayIdealClass_mul,
    rayIdealClass_eq_some F m hm _ hzn hzc] at hA hB
  cases hca : rayIdealClass F m hm (Ideal.span {α}) with
  | none => simp [hca] at hA
  | some ca =>
    cases hcb : rayIdealClass F m hm (Ideal.span {β}) with
    | none => simp [hcb] at hB
    | some cb =>
      apply congrArg some
      have hAa : ca * (QuotientGroup.mk' _ (rayIdealClassRepresentative F m hm _ hzn hzc) : RayIdealClass F m hm) = 1 := Option.some.inj (by simpa [hca] using hA)
      have hBb : cb * (QuotientGroup.mk' _ (rayIdealClassRepresentative F m hm _ hzn hzc) : RayIdealClass F m hm) = 1 := Option.some.inj (by simpa [hcb] using hB)
      have hh := congrArg (fun c : RayIdealClass F m hm => c * (QuotientGroup.mk' _ (rayIdealClassRepresentative F m hm _ hzn hzc) : RayIdealClass F m hm)⁻¹) (hAa.trans hBb.symm)
      simpa only [mul_inv_cancel_right] using hh

variable (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (E : RayCharacterData F m hm η)

local notation "Iₐ" => rayIdealFractionalIdeal F a ha
local notation "M" => rayIdealFractionalIdeal F m hm
local notation "Rₐ" => coprimeIdealResidue F m a hm ha
local notation "Rₐˣ" => coprimeIdealResidueUnits F m a hm ha hcop hmt
local notation "πₐ" => fractionalIdealQuotientMk
  (Iₐ : FractionalIdeal (𝓞 F)⁰ F) ((Iₐ * M) : FractionalIdeal (𝓞 F)⁰ F)
include hF hcop hmt E

theorem coprimeIdealResidueUnits_lift_ne_zero
    (q : Rₐˣ) (x : {x : F // x ∈ (Iₐ : FractionalIdeal (𝓞 F)⁰ F)})
    (hx : πₐ x = q.val) : x.val ≠ 0 := by
  letI : Nontrivial (𝓞 F ⧸ m) := Ideal.Quotient.nontrivial_iff.mpr hmt
  intro hzero
  have hπzero : πₐ x = 0 :=
    (fractionalIdealQuotientMk_eq_zero_iff _ _ x).mpr (hzero ▸ (Iₐ * M).val.zero_mem)
  have hqzero : q.val = 0 := hx.symm.trans hπzero
  have hunit := q.property
  rw [hqzero, map_zero] at hunit
  exact not_isUnit_zero hunit

theorem coprimeIdealResidueUnits_integralElementIdeal_ne_bot
    (q : Rₐˣ) (x : {x : F // x ∈ (Iₐ : FractionalIdeal (𝓞 F)⁰ F)})
    (hx : πₐ x = q.val) : integralElementIdeal Iₐ x ≠ ⊥ := by
  have hxne := coprimeIdealResidueUnits_lift_ne_zero hF m a hm ha hcop hmt η E q x hx
  intro hbot
  have hz : FractionalIdeal.spanSingleton (𝓞 F)⁰ x.val *
      (Iₐ : FractionalIdeal (𝓞 F)⁰ F)⁻¹ = 0 := by
    rw [← integralElementIdeal_coe, hbot, FractionalIdeal.coeIdeal_bot]
  have hspan : FractionalIdeal.spanSingleton (𝓞 F)⁰ x.val = 0 := by
    calc
      _ = (FractionalIdeal.spanSingleton (𝓞 F)⁰ x.val *
          (Iₐ : FractionalIdeal (𝓞 F)⁰ F)⁻¹) * Iₐ := by
        rw [mul_assoc, ← Units.val_inv_eq_inv_val, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, mul_one]
      _ = 0 := by rw [hz, zero_mul]
  exact hxne (FractionalIdeal.spanSingleton_eq_zero_iff.mp hspan)

theorem coprimeIdealResidueUnits_integralElementIdeal_coprime
    (q : Rₐˣ) (x : {x : F // x ∈ (Iₐ : FractionalIdeal (𝓞 F)⁰ F)})
    (hx : πₐ x = q.val) : integralElementIdeal Iₐ x ⊔ m = ⊤ := by
  classical
  obtain ⟨α, hα, hαx⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 F)⁰).mp x.property
  have hxα : x = ⟨(algebraMap (𝓞 F) F) α, coprimeIdealResidue_mem a ha α hα⟩ :=
    Subtype.ext hαx.symm
  have hu : IsUnit (Ideal.Quotient.mk m α) := by
    have h := q.property
    rw [← hx, hxα, coprimeIdealResidueReduction_mk m a hm ha hcop α hα] at h
    exact h
  obtain ⟨u, hu⟩ := hu
  obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (↑(u⁻¹) : 𝓞 F ⧸ m)
  have hab : α * β - 1 ∈ m := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, map_one, ← hu, hβ]
    simp
  have hprincipal : Ideal.span {α} ⊔ m = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have hαβ : α * β ∈ Ideal.span {α} ⊔ m :=
      Ideal.mem_sup_left (Ideal.mul_mem_right β _ (Ideal.subset_span (by simp)))
    have hd : α * β - 1 ∈ Ideal.span {α} ⊔ m := Ideal.mem_sup_right hab
    simpa using (Ideal.span {α} ⊔ m).sub_mem hαβ hd
  have hproduct : integralElementIdeal Iₐ x * a = Ideal.span {α} := by
    apply FractionalIdeal.coeIdeal_injective (K := F)
    change ((integralElementIdeal Iₐ x * a : Ideal (𝓞 F)) :
      FractionalIdeal (𝓞 F)⁰ F) = (Ideal.span {α} : FractionalIdeal (𝓞 F)⁰ F)
    rw [FractionalIdeal.coeIdeal_mul, integralElementIdeal_coe, ← hαx,
      ← FractionalIdeal.coeIdeal_span_singleton]
    change ((Ideal.span {α} : FractionalIdeal (𝓞 F)⁰ F) *
      (Iₐ : FractionalIdeal (𝓞 F)⁰ F)⁻¹) * Iₐ = _
    rw [mul_assoc, ← Units.val_inv_eq_inv_val, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, mul_one]
  apply top_unique
  rw [← hprincipal, ← hproduct]
  exact sup_le_sup_right Ideal.mul_le_left m

theorem ResidueCoefficientAux.unit_iff_support
    (x : {x : F // x ∈ (Iₐ : FractionalIdeal (𝓞 F)⁰ F)}) :
    IsUnit (coprimeIdealResidueReduction F m a hm ha hcop (πₐ x)) ↔
      integralElementIdeal Iₐ x ≠ ⊥ ∧ integralElementIdeal Iₐ x ⊔ m = ⊤ := by
  constructor
  · intro hu
    let q : Rₐˣ := ⟨πₐ x, hu⟩
    exact ⟨coprimeIdealResidueUnits_integralElementIdeal_ne_bot
      hF m a hm ha hcop hmt η E q x rfl,
      coprimeIdealResidueUnits_integralElementIdeal_coprime
      hF m a hm ha hcop hmt η E q x rfl⟩
  · rintro ⟨_, hc⟩
    obtain ⟨α, hα, hαx⟩ := ResidueCoefficientAux.integral_lift a ha x
    have hxα : x = ⟨(algebraMap (𝓞 F) F) α, coprimeIdealResidue_mem a ha α hα⟩ :=
      Subtype.ext hαx.symm
    rw [hxα, coprimeIdealResidueReduction_mk m a hm ha hcop α hα]
    apply (ResidueCoefficientAux.quotient_unit_iff m α).mpr
    rw [← ResidueCoefficientAux.coefficient_mul a ha x α hαx,
      Ideal.mul_sup_eq_of_coprime_left hc]
    exact hcop

theorem ResidueCoefficientAux.ordinary_fiber
    (x : {x : F // x ∈ (Iₐ : FractionalIdeal (𝓞 F)⁰ F)})
    (hn : integralElementIdeal Iₐ x ≠ ⊥) :
    ClassGroup.mk F (rayIdealFractionalIdeal F (integralElementIdeal Iₐ x) hn) =
      (ClassGroup.mk F Iₐ)⁻¹ := by
  have hp : ClassGroup.mk F
      (rayIdealFractionalIdeal F (integralElementIdeal Iₐ x) hn * Iₐ) = 1 := by
    apply ClassGroup.mk_eq_one_iff.mpr
    apply (FractionalIdeal.isPrincipal_iff _).mpr
    refine ⟨x.val, ?_⟩
    change (integralElementIdeal Iₐ x : FractionalIdeal (𝓞 F)⁰ F) *
      (Iₐ : FractionalIdeal (𝓞 F)⁰ F) = _
    rw [integralElementIdeal_coe, mul_assoc, ← Units.val_inv_eq_inv_val,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  rw [map_mul] at hp
  exact eq_inv_of_mul_eq_one_left hp

theorem coprimeIdealResidueUnits_rayIdealClass_lift_independent
    (q : Rₐˣ)
    (x y : {x : F // x ∈ (Iₐ : FractionalIdeal (𝓞 F)⁰ F)})
    (hx : πₐ x = q.val) (hy : πₐ y = q.val) :
    rayIdealClass F m hm (integralElementIdeal Iₐ x) =
      rayIdealClass F m hm (integralElementIdeal Iₐ y) := by
  obtain ⟨α, hα, hαx⟩ := ResidueCoefficientAux.integral_lift a ha x
  obtain ⟨β, hβ, hβy⟩ := ResidueCoefficientAux.integral_lift a ha y
  have hxα : x = ⟨algebraMap (𝓞 F) F α, coprimeIdealResidue_mem a ha α hα⟩ :=
    Subtype.ext hαx.symm
  have hyβ : y = ⟨algebraMap (𝓞 F) F β, coprimeIdealResidue_mem a ha β hβ⟩ :=
    Subtype.ext hβy.symm
  have hres : Ideal.Quotient.mk m α = Ideal.Quotient.mk m β := by
    have hh := congrArg (coprimeIdealResidueReduction F m a hm ha hcop) (hx.trans hy.symm)
    rw [hxα, hyβ, coprimeIdealResidueReduction_mk m a hm ha hcop α hα,
      coprimeIdealResidueReduction_mk m a hm ha hcop β hβ] at hh
    exact hh
  have hu : IsUnit (Ideal.Quotient.mk m α) := by
    have hh := q.property
    rw [← hx, hxα, coprimeIdealResidueReduction_mk m a hm ha hcop α hα] at hh
    exact hh
  have hp := principal_ray_compatible hF m hm hmt α β hu hres
  rw [← ResidueCoefficientAux.coefficient_mul a ha x α hαx,
    ← ResidueCoefficientAux.coefficient_mul a ha y β hβy,
    rayIdealClass_mul, rayIdealClass_mul,
    rayIdealClass_eq_some F m hm a ha hcop] at hp
  have hxn := coprimeIdealResidueUnits_integralElementIdeal_ne_bot hF m a hm ha hcop hmt η E q x hx
  have hxc := coprimeIdealResidueUnits_integralElementIdeal_coprime hF m a hm ha hcop hmt η E q x hx
  have hyn := coprimeIdealResidueUnits_integralElementIdeal_ne_bot hF m a hm ha hcop hmt η E q y hy
  have hyc := coprimeIdealResidueUnits_integralElementIdeal_coprime hF m a hm ha hcop hmt η E q y hy
  rw [rayIdealClass_eq_some F m hm _ hxn hxc,
    rayIdealClass_eq_some F m hm _ hyn hyc] at hp ⊢
  apply congrArg some
  have hh := congrArg (fun c : RayIdealClass F m hm => c *
    (QuotientGroup.mk' _ (rayIdealClassRepresentative F m hm a ha hcop) : RayIdealClass F m hm)⁻¹)
    (Option.some.inj hp)
  simpa only [mul_inv_cancel_right] using hh

theorem integralElementIdeal_coefficient_congr
    (x y : {x : F // x ∈ (Iₐ : FractionalIdeal (𝓞 F)⁰ F)})
    (hxy : x.val - y.val ∈ ((Iₐ * M) : FractionalIdeal (𝓞 F)⁰ F)) :
    η (integralElementIdeal Iₐ x) = η (integralElementIdeal Iₐ y) := by
  classical
  have heq : πₐ x = πₐ y := by
    apply sub_eq_zero.mp
    rw [← map_sub, fractionalIdealQuotientMk_eq_zero_iff]
    exact hxy
  by_cases hu : IsUnit (coprimeIdealResidueReduction F m a hm ha hcop (πₐ x))
  · let q : Rₐˣ := ⟨πₐ x, hu⟩
    rw [E.descent, E.descent,
      coprimeIdealResidueUnits_rayIdealClass_lift_independent
        hF m a hm ha hcop hmt η E q x y rfl heq.symm]
  · have hv : ¬ IsUnit (coprimeIdealResidueReduction F m a hm ha hcop (πₐ y)) := by
      simpa only [heq] using hu
    have hn (z : {z : F // z ∈ (Iₐ : FractionalIdeal (𝓞 F)⁰ F)})
        (hz : ¬ IsUnit (coprimeIdealResidueReduction F m a hm ha hcop (πₐ z))) :
        rayIdealClass F m hm (integralElementIdeal Iₐ z) = none := by
      apply rayIdealClass_eq_none
      have hs := (ResidueCoefficientAux.unit_iff_support hF m a hm ha hcop hmt η E z).not.mp hz
      tauto
    rw [E.descent, E.descent, hn x hu, hn y hv]

omit hF hcop hmt E

def coprimeIdealResidueCoefficient (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (E : RayCharacterData F m hm η) : coprimeIdealResidue F m a hm ha → ℂ := by
  exact fun q => η (integralElementIdeal (rayIdealFractionalIdeal F a ha)
    (Classical.choose (fractionalIdealQuotientMk_surjective
      (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
      ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
        FractionalIdeal (𝓞 F)⁰ F) q)))

def coprimeIdealResidueRayClass (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤) :
    coprimeIdealResidueUnits F m a hm ha hcop hmt →
      {c : RayIdealClass F m hm //
        rayToOrdinary F m hm c = (ClassGroup.mk F (rayIdealFractionalIdeal F a ha))⁻¹} := by
  intro q
  let η₀ := rayCharacterOfGroupCharacter F m hm 1
  let E₀ := chooseRayCharacterData (hm := hm) η₀
  let x := Classical.choose (fractionalIdealQuotientMk_surjective
    (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
    ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
      FractionalIdeal (𝓞 F)⁰ F) q.val)
  have hx := Classical.choose_spec (fractionalIdealQuotientMk_surjective
    (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
    ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
      FractionalIdeal (𝓞 F)⁰ F) q.val)
  have hn := coprimeIdealResidueUnits_integralElementIdeal_ne_bot
    hF m a hm ha hcop hmt η₀ E₀ q x hx
  have hc := coprimeIdealResidueUnits_integralElementIdeal_coprime
    hF m a hm ha hcop hmt η₀ E₀ q x hx
  refine ⟨QuotientGroup.mk' _ (rayIdealClassRepresentative F m hm _ hn hc), ?_⟩
  rw [rayToOrdinary_rayIdealClass hm _ hn hc _
    (rayIdealClass_eq_some F m hm _ hn hc)]
  exact ResidueCoefficientAux.ordinary_fiber hF m a hm ha hcop hmt η₀ E₀ x hn

include hF hcop hmt E

local notation "κₐ" => coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E
local notation "rₐ" => coprimeIdealResidueRayClass hF m a hm ha hcop hmt

@[simp] theorem coprimeIdealResidueCoefficient_mk
    (x : {x : F // x ∈ (Iₐ : FractionalIdeal (𝓞 F)⁰ F)}) :
    κₐ (πₐ x) = η (integralElementIdeal Iₐ x) := by
  classical
  let y := Classical.choose (fractionalIdealQuotientMk_surjective
    (Iₐ : FractionalIdeal (𝓞 F)⁰ F) ((Iₐ * M) : FractionalIdeal (𝓞 F)⁰ F) (πₐ x))
  have hy : πₐ y = πₐ x := Classical.choose_spec (fractionalIdealQuotientMk_surjective
    (Iₐ : FractionalIdeal (𝓞 F)⁰ F) ((Iₐ * M) : FractionalIdeal (𝓞 F)⁰ F) (πₐ x))
  apply integralElementIdeal_coefficient_congr hF m a hm ha hcop hmt η E y x
  exact (fractionalIdealQuotientMk_eq_zero_iff _ _ (y-x)).mp (by
    rw [map_sub, hy, sub_self])

theorem coprimeIdealResidueCoefficient_eq_zero_of_not_isUnit
    (q : Rₐ) (hq : ¬ IsUnit (coprimeIdealResidueReduction F m a hm ha hcop q)) :
    κₐ q = 0 := by
  classical
  obtain ⟨x, hx⟩ := fractionalIdealQuotientMk_surjective
    (Iₐ : FractionalIdeal (𝓞 F)⁰ F) ((Iₐ * M) : FractionalIdeal (𝓞 F)⁰ F) q
  have hs : ¬ (integralElementIdeal Iₐ x ≠ ⊥ ∧ integralElementIdeal Iₐ x ⊔ m = ⊤) := by
    intro h
    apply hq
    rw [← hx]
    exact (ResidueCoefficientAux.unit_iff_support hF m a hm ha hcop hmt η E x).mpr h
  have he : integralElementIdeal Iₐ x = ⊥ ∨ integralElementIdeal Iₐ x ⊔ m ≠ ⊤ := by
    tauto
  rw [← hx, coprimeIdealResidueCoefficient_mk, E.descent,
    rayIdealClass_eq_none F m hm _ he]

theorem coprimeIdealResidueRayClass_lift
    (q : Rₐˣ) (x : {x : F // x ∈ (Iₐ : FractionalIdeal (𝓞 F)⁰ F)})
    (hx : πₐ x = q.val) :
    rayIdealClass F m hm (integralElementIdeal Iₐ x) = some (rₐ q).val := by
  classical
  let y := Classical.choose (fractionalIdealQuotientMk_surjective
    (Iₐ : FractionalIdeal (𝓞 F)⁰ F) ((Iₐ * M) : FractionalIdeal (𝓞 F)⁰ F) q.val)
  have hy : πₐ y = q.val := Classical.choose_spec (fractionalIdealQuotientMk_surjective
    (Iₐ : FractionalIdeal (𝓞 F)⁰ F) ((Iₐ * M) : FractionalIdeal (𝓞 F)⁰ F) q.val)
  rw [coprimeIdealResidueUnits_rayIdealClass_lift_independent hF m a hm ha hcop hmt η E q x y hx hy]
  exact rayIdealClass_eq_some F m hm _ _ _

theorem coprimeIdealResidueCoefficient_eq_character (q : Rₐˣ) :
    κₐ q.val = E.ψ (rₐ q).val := by
  obtain ⟨x, hx⟩ := fractionalIdealQuotientMk_surjective
    (Iₐ : FractionalIdeal (𝓞 F)⁰ F) ((Iₐ * M) : FractionalIdeal (𝓞 F)⁰ F) q.val
  rw [← hx, coprimeIdealResidueCoefficient_mk, E.descent,
    coprimeIdealResidueRayClass_lift hF m a hm ha hcop hmt η E q x hx]

theorem coprimeIdealResidueRayClass_unit_invariant :
    letI := coprimeIdealResidueUnitAction F m a hm ha hcop hmt
    ∀ (ε : residueUnitImage F m) (q : Rₐˣ), rₐ (ε • q) = rₐ q := by
  letI := coprimeIdealResidueUnitAction F m a hm ha hcop hmt
  intro ε q
  obtain ⟨u, hu⟩ := ε.property
  obtain ⟨x, hx⟩ := fractionalIdealQuotientMk_surjective
    (Iₐ : FractionalIdeal (𝓞 F)⁰ F) ((Iₐ * M) : FractionalIdeal (𝓞 F)⁰ F) q.val
  let y := (u : 𝓞 F) • x
  have hy : πₐ y = (ε • q).val := by
    apply (coprimeIdealResidueReduction F m a hm ha hcop).injective
    have hact := coprimeIdealResidueUnitAction_apply m a hm ha hcop hmt ε q
    have hb := congrArg (fun v : (𝓞 F ⧸ m)ˣ => (v : 𝓞 F ⧸ m)) hact
    simp only [coprimeIdealResidueUnitsEquiv_coe, Units.val_mul] at hb
    rw [hb, ← hu]
    change coprimeIdealResidueReduction F m a hm ha hcop (πₐ ((u : 𝓞 F) • x)) = _
    rw [map_smul, map_smul, hx]
    rfl
  have hi : integralElementIdeal Iₐ y = integralElementIdeal Iₐ x := by
    apply FractionalIdeal.coeIdeal_injective (K := F)
    change (integralElementIdeal Iₐ y : FractionalIdeal (𝓞 F)⁰ F) =
      (integralElementIdeal Iₐ x : FractionalIdeal (𝓞 F)⁰ F)
    rw [integralElementIdeal_coe, integralElementIdeal_coe]
    change FractionalIdeal.spanSingleton (𝓞 F)⁰ ((algebraMap (𝓞 F) F) u.val * x.val) * _ = _
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← FractionalIdeal.coeIdeal_span_singleton,
      Ideal.span_singleton_eq_top.mpr u.isUnit, FractionalIdeal.coeIdeal_top, one_mul]
  apply Subtype.ext
  apply Option.some.inj
  rw [← coprimeIdealResidueRayClass_lift hF m a hm ha hcop hmt η E (ε • q) y hy,
    ← coprimeIdealResidueRayClass_lift hF m a hm ha hcop hmt η E q x hx, hi]

end DedekindZetaZeroFree.Hecke.Theta

end
