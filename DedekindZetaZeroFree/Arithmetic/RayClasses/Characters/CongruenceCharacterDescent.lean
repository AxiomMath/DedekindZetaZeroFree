module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.ModulusIdeal

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.PrimitiveRay

variable {F : Type} [Field F] [NumberField F]

private theorem cast_ray_mk
    {a b : ClassFieldTheory.RayClassModulus F} (h : a = b)
    (x : ClassFieldTheory.NumberFieldFractionalIdealGroup F)
    (ha : x ∈ ClassFieldTheory.rayClassPrimeToIdeals a)
    (hb : x ∈ ClassFieldTheory.rayClassPrimeToIdeals b) :
    (MulEquiv.cast (M := ClassFieldTheory.RayClassGroup) h)
      (QuotientGroup.mk (⟨x, ha⟩ : ClassFieldTheory.rayClassPrimeToIdeals a)) =
      QuotientGroup.mk (⟨x, hb⟩ : ClassFieldTheory.rayClassPrimeToIdeals b) := by
  cases h
  rfl

theorem rayDescent (hc : NumberField.IsTotallyComplex F)
    (Φ : IdeleClassGroup F →* ℂˣ)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (hdefining :
      (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal
        F (RayClassBridge.narrowIdealModulus F m hm)).congruenceSubgroup ≤ Φ.ker) :
    ∃ (ρ : ClassFieldTheory.RayClassGroup
          (RayClassBridge.narrowIdealModulus F m hm) →* ℂˣ)
      (ρ₀ : ClassFieldTheory.RayClassGroup (M F m hm) →* ℂˣ)
      (χ : RayClassCharacter F m),
      χ = frozenRay F hc m hm ρ₀ ∧
      (∀ I : Ideal (𝓞 F), χ I =
        if h : I ≠ ⊥ ∧ I ⊔ m = ⊤ then
          (ρ (RayClassBridge.integralRayClass F m hm I h.1 h.2) : ℂ)
        else 0) ∧
      (∀ c : IdeleClassGroup F,
        ρ ((ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele
          F (RayClassBridge.narrowIdealModulus F m hm)).symm
            (QuotientGroup.mk'
              (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal
                F (RayClassBridge.narrowIdealModulus F m hm)).congruenceSubgroup c)) = Φ c) ∧
      (∀ c : IdeleClassGroup F,
        RayClassBridge.ideleClassCharacter F hc m hm χ c = Φ c) := by
  let N := RayClassBridge.narrowIdealModulus F m hm
  let H := (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F N).congruenceSubgroup
  let e := ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele F N
  let ρ : ClassFieldTheory.RayClassGroup N →* ℂˣ :=
    (QuotientGroup.lift H Φ hdefining).comp e.toMonoidHom
  letI : IsEmpty (ClassFieldTheory.RayClassRealPlace F) :=
    ⟨fun v => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
      (hc.isComplex v.val)) v.property⟩
  have hMN : M F m hm = N := by
    apply ClassFieldTheory.RayClassModulus.ext
    · rfl
    · exact Subsingleton.elim _ _
  let t : ClassFieldTheory.RayClassGroup (M F m hm) ≃*
      ClassFieldTheory.RayClassGroup N := MulEquiv.cast (M := ClassFieldTheory.RayClassGroup) hMN
  let ρ₀ := ρ.comp t.toMonoidHom
  let χ := frozenRay F hc m hm ρ₀
  have ht (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤) :
      t (frozenIntegralRayClass F m hm I hI hcop) =
        RayClassBridge.integralRayClass F m hm I hI hcop := by
    exact cast_ray_mk hMN (RayClassBridge.integralUnit F I hI) _ _
  have heval (I : Ideal (𝓞 F)) : χ I =
      if h : I ≠ ⊥ ∧ I ⊔ m = ⊤ then
        (ρ (RayClassBridge.integralRayClass F m hm I h.1 h.2) : ℂ) else 0 := by
    rw [frozenRay_apply]
    split_ifs with h
    · change (ρ (t (frozenIntegralRayClass F m hm I h.1 h.2)) : ℂ) = _
      rw [ht]
    · rfl
  have hρ (c : IdeleClassGroup F) : ρ (e.symm (QuotientGroup.mk' H c)) = Φ c := by
    change (QuotientGroup.lift H Φ hdefining) (e (e.symm (QuotientGroup.mk' H c))) = _
    rw [e.apply_symm_apply]
    exact QuotientGroup.lift_mk' H hdefining c
  have hfrac : ρ.comp (QuotientGroup.mk'
      (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo N)) =
      RayClassBridge.fractionalCharacter F m hm χ := by
    apply RayClassBridge.fractionalCharacter_unique F m hm χ
    intro I hI hcop
    change (ρ (RayClassBridge.integralRayClass F m hm I hI hcop) : ℂ) = χ I
    rw [heval, dif_pos ⟨hI, hcop⟩]
  have hray : ρ = RayClassBridge.rayCharacter F hc m hm χ := by
    apply MonoidHom.ext
    intro c
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
      (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo N) c
    have h := DFunLike.congr_fun hfrac a
    have h' := DFunLike.congr_fun (RayClassBridge.rayCharacter_comp_quotient F hc m hm χ) a
    exact h.trans h'.symm
  refine ⟨ρ, ρ₀, χ, rfl, heval, hρ, ?_⟩
  intro c
  change RayClassBridge.rayCharacter F hc m hm χ (e.symm (QuotientGroup.mk' H c)) = Φ c
  rw [← hray]
  exact hρ c

end DedekindZetaZeroFree.PrimitiveRay

end
