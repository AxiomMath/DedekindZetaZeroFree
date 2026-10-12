module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterTrivialityOnPrincipalCongruenceIdeals
public import DedekindZetaZeroFree.Algebra.FiniteGroupCharacters.UnitNorm

@[expose] public section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.RayClassBridge

 theorem fractionalCharacter_principal_kernel
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪) :
    ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo (narrowIdealModulus F 𝔪 h𝔪) ≤
      (fractionalCharacter F 𝔪 h𝔪 η).ker := by
  exact fractionalCharacter_kills_rayPrincipal F hcomplex 𝔪 h𝔪 η

def rayCharacter
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪) :
    ClassFieldTheory.RayClassGroup (narrowIdealModulus F 𝔪 h𝔪) →* ℂˣ :=
  QuotientGroup.lift
    (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo (narrowIdealModulus F 𝔪 h𝔪))
    (fractionalCharacter F 𝔪 h𝔪 η)
    (fractionalCharacter_principal_kernel F hcomplex 𝔪 h𝔪 η)

theorem rayCharacter_comp_quotient
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪) :
    (rayCharacter F hcomplex 𝔪 h𝔪 η).comp
      (QuotientGroup.mk'
        (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo
          (narrowIdealModulus F 𝔪 h𝔪))) = fractionalCharacter F 𝔪 h𝔪 η := by
  rfl

@[simp] theorem rayCharacter_integral
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤) :
    (rayCharacter F hcomplex 𝔪 h𝔪 η (integralRayClass F 𝔪 h𝔪 I hI hcop) : ℂ) =
      η I := by
  change (fractionalCharacter F 𝔪 h𝔪 η (integralPrimeTo F 𝔪 h𝔪 I hI hcop) : ℂ) = η I
  exact fractionalCharacter_integral F 𝔪 h𝔪 η I hI hcop

theorem rayClassGroup_card_pos
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) :
    0 < Nat.card (ClassFieldTheory.RayClassGroup (narrowIdealModulus F 𝔪 h𝔪)) := by
  letI := ClassFieldTheory.rayClassGroup_finite F (narrowIdealModulus F 𝔪 h𝔪)
  exact Nat.card_pos

theorem rayCharacter_pow_card
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (c : ClassFieldTheory.RayClassGroup (narrowIdealModulus F 𝔪 h𝔪)) :
    rayCharacter F hcomplex 𝔪 h𝔪 η c ^
      Nat.card (ClassFieldTheory.RayClassGroup (narrowIdealModulus F 𝔪 h𝔪)) = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

@[simp] theorem rayCharacter_norm
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (c : ClassFieldTheory.RayClassGroup (narrowIdealModulus F 𝔪 h𝔪)) :
    ‖(rayCharacter F hcomplex 𝔪 h𝔪 η c : ℂ)‖ = 1 := by
  letI := ClassFieldTheory.rayClassGroup_finite F (narrowIdealModulus F 𝔪 h𝔪)
  exact FiniteOrder.norm_eq_one _ c

theorem rayClassCharacter_norm_of_ne_zero
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (I : Ideal (𝓞 F)) (hηI : η I ≠ 0) : ‖η I‖ = 1 := by
  obtain ⟨hI, hcop⟩ := (rayClassCharacter_ne_zero_iff F 𝔪 η I).mp hηI
  rw [← rayCharacter_integral F hcomplex 𝔪 h𝔪 η I hI hcop]
  exact rayCharacter_norm F hcomplex 𝔪 h𝔪 η _

theorem rayClassCharacter_norm_of_primeTo
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤) : ‖η I‖ = 1 := by
  exact rayClassCharacter_norm_of_ne_zero F hcomplex 𝔪 h𝔪 η I
    ((rayClassCharacter_ne_zero_iff F 𝔪 η I).mpr ⟨hI, hcop⟩)

end DedekindZetaZeroFree.RayClassBridge

end
