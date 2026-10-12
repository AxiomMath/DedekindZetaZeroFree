module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.FractionalCharacterExtensionUniqueness
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.PositiveIntegralGenerators
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.IntegralPrincipalCongruence
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassGroupFinite

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

def descendedCharacter (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) :
    ClassFieldTheory.RayClassGroup (fullModulus m hm) →* ℂˣ := by
  refine QuotientGroup.lift
    (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo (fullModulus m hm))
    (fractionalCharacter m hm η) ?_
  intro J hJ
  change fractionalCharacter m hm η J = 1
  have hmem : (J : ClassFieldTheory.NumberFieldFractionalIdealGroup F) ∈
      ClassFieldTheory.rayPrincipalIdealSubgroup (fullModulus m hm) := hJ
  obtain ⟨x, hx, hxeq⟩ :=
    (ClassFieldTheory.mem_rayPrincipalIdealSubgroup_iff (fullModulus m hm) J).mp hmem
  obtain ⟨a, b, ha, hb, hab, ha1, hb1, hapos, hbpos⟩ :=
    exists_positive_integral_generator m hm x hx
  have hcop : ∀ c : 𝓞 F, c - 1 ∈ m → Ideal.span {c} ⊔ m = ⊤ := by
    intro c hc
    apply (Ideal.eq_top_iff_one _).mpr
    have hc' : c ∈ Ideal.span {c} ⊔ m :=
      Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton c))
    have hc1' : c - 1 ∈ Ideal.span {c} ⊔ m := Ideal.mem_sup_right hc
    simpa using (Ideal.span {c} ⊔ m).sub_mem hc' hc1'
  have haI : Ideal.span {a} ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp ha
  have hbI : Ideal.span {b} ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp hb
  have hxratio : x = Units.mk0 (a : F) (by exact_mod_cast ha) *
      (Units.mk0 (b : F) (by exact_mod_cast hb))⁻¹ := by
    apply Units.ext
    change (x : F) = (a : F) * (b : F)⁻¹
    rw [hab, mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hb), mul_one]
  have hratio : (J : ClassFieldTheory.NumberFieldFractionalIdealGroup F) =
      integralIdealUnit (Ideal.span {a}) haI *
        (integralIdealUnit (Ideal.span {b}) hbI)⁻¹ := by
    rw [← hxeq, hxratio, map_mul, map_inv,
      principal_integral_span a ha, principal_integral_span b hb]
  apply Units.ext
  change (fractionalCharacter m hm η J : ℂ) = 1
  rw [fractionalCharacter_apply_ratio m hm η _ _ haI hbI
    (hcop a ha1) (hcop b hb1) J hratio,
    η.map_span' a ha ha1 hapos, η.map_span' b hb hb1 hbpos, one_div, inv_one]

@[simp] theorem descendedCharacter_apply_idealClass
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤) :
    (descendedCharacter m hm η (idealClass m hm I hI hcop) : ℂ) = η I := by
  change (fractionalCharacter m hm η (idealToPrimeTo m hm I hI hcop) : ℂ) = η I
  exact fractionalCharacter_apply m hm η I hI hcop

theorem descendedCharacter_unique (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (ψ : ClassFieldTheory.RayClassGroup (fullModulus m hm) →* ℂˣ)
    (hψ : ∀ (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤),
      (ψ (idealClass m hm I hI hcop) : ℂ) = η I) :
    ψ = descendedCharacter m hm η := by
  apply QuotientGroup.monoidHom_ext
  rw [descendedCharacter, QuotientGroup.lift_comp_mk']
  apply fractionalCharacter_unique m hm η
  intro I hI hcop
  exact hψ I hI hcop

end DedekindZetaZeroFree.LargeSieve.RayBridge

end
