module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.FractionalIdealQuotientCharacters
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.CongruentDenominatorClearing

@[expose] public section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.RayClassBridge

theorem fractionalCharacter_kills_rayPrincipal
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪) :
    ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo (narrowIdealModulus F 𝔪 h𝔪) ≤
      (fractionalCharacter F 𝔪 h𝔪 η).ker := by
  letI := hF
  intro I hI
  rw [ClassFieldTheory.GlobalClassFieldComparison.rayPrincipalIdealSubgroup_eq] at hI
  obtain ⟨x, hx, hxi⟩ := (RayClass.mem_principalRayIdealSubgroup_iff
    (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal
      F (narrowIdealModulus F 𝔪 h𝔪)) I).mp hI
  have hxray :=
    (ClassFieldTheory.GlobalClassFieldComparison.principalIdele_mem_primeTo_iff_isRayCongruent
      F (narrowIdealModulus F 𝔪 h𝔪) x).mp hx
  obtain ⟨α, β, hα, hβ, hcα, hcβ, hab⟩ :=
    isRayCongruent_clear_denominators F hF 𝔪 h𝔪 x hxray
  have hA : Ideal.span {α} ≠ ⊥ := fun h => hα (Ideal.span_singleton_eq_bot.mp h)
  have hB : Ideal.span {β} ≠ ⊥ := fun h => hβ (Ideal.span_singleton_eq_bot.mp h)
  have hcA := span_add_modulus_eq_top_of_sub_one_mem F 𝔪 α hcα
  have hcB := span_add_modulus_eq_top_of_sub_one_mem F 𝔪 β hcβ
  have hpos : ∀ (a : 𝓞 F) (φ : F →+* ℝ), 0 < φ (a : F) := by
    intro a φ
    exfalso
    apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal
      (Complex.ofRealHom.comp φ)
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext z
    simp [NumberField.ComplexEmbedding.conjugate]
  have hvalα : η (Ideal.span {α}) = 1 := η.map_span' α hα hcα (hpos α)
  have hvalβ : η (Ideal.span {β}) = 1 := η.map_span' β hβ hcβ (hpos β)
  have hquot : I = integralPrimeTo F 𝔪 h𝔪 (Ideal.span {α}) hA hcA *
      (integralPrimeTo F 𝔪 h𝔪 (Ideal.span {β}) hB hcB)⁻¹ := by
    apply Subtype.ext
    rw [← hxi]
    change toPrincipalIdeal (𝓞 F) F x =
      integralUnit F (Ideal.span {α}) hA * (integralUnit F (Ideal.span {β}) hB)⁻¹
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, integralUnit_val,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_inv,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    have hβF : (β : F) ≠ 0 := by
      exact_mod_cast hβ
    change (x : F) = (α : F) * (β : F)⁻¹
    rw [hab, mul_assoc, mul_inv_cancel₀ hβF, mul_one]
  rw [MonoidHom.mem_ker]
  apply Units.ext
  change (fractionalCharacter F 𝔪 h𝔪 η I : ℂ) = 1
  rw [hquot, fractionalCharacter_quotient, hvalα, hvalβ, div_self one_ne_zero]

end DedekindZetaZeroFree.RayClassBridge

end
