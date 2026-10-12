module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.IntegralIdealClassOperations
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.PrincipalCriterion

@[expose] public section

noncomputable section

open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.AbelianQuotient

def rayCharacterOfGroupCharacter
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (ψ : RayIdealClass K m hm →* ℂˣ) :
    DedekindZetaZeroFree.RayClassCharacter K m where
  toFun I := match rayIdealClass K m hm I with
    | none => 0
    | some a => (ψ a : ℂ)
  map_mul' I J := by
    rw [rayIdealClass_mul]
    cases hI : rayIdealClass K m hm I <;>
      cases hJ : rayIdealClass K m hm J <;> simp [hI, hJ]
  map_top' := by simp
  eq_zero_iff' I := by
    rw [← rayIdealClass_eq_none_iff K m hm I]
    cases hI : rayIdealClass K m hm I <;> simp
  map_span' α hα hcong hpos := by
    rw [rayIdealClass_span K m hm α hα hcong hpos]
    simp

@[simp] theorem rayCharacterOfGroupCharacter_apply
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (ψ : RayIdealClass K m hm →* ℂˣ)
    (I : Ideal (𝓞 K)) :
    rayCharacterOfGroupCharacter K m hm ψ I =
      match rayIdealClass K m hm I with
      | none => 0
      | some a => (ψ a : ℂ) := by
  rfl

theorem rayCharacterOfGroupCharacter_finitePrime
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (ψ : RayIdealClass K m hm →* ℂˣ)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∉ (narrowIdealModulus K m hm).finitePart.support) :
    rayCharacterOfGroupCharacter K m hm ψ p.asIdeal =
      (ψ (ClassFieldTheory.rayClassOfFinitePrime (narrowIdealModulus K m hm) p hp) : ℂ) := by
  rw [rayCharacterOfGroupCharacter_apply, rayIdealClass_of_finitePrime K m hm p hp]

theorem rayCharacterOfGroupCharacter_isPrincipal_iff
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (ψ : RayIdealClass K m hm →* ℂˣ) :
    (rayCharacterOfGroupCharacter K m hm ψ).IsPrincipal ↔ ψ = 1 := by
  rw [rayCharacterPrincipalCriterion K m hm
    (rayCharacterOfGroupCharacter K m hm ψ) ((Units.coeHom ℂ).comp ψ)
    (fun I => rayCharacterOfGroupCharacter_apply K m hm ψ I)]
  constructor
  · intro h
    apply MonoidHom.ext
    intro a
    apply Units.ext
    exact congrArg (fun f : RayIdealClass K m hm →* ℂ => f a) h
  · intro h
    subst ψ
    apply MonoidHom.ext
    intro a
    simp

end DedekindZetaZeroFree.AbelianQuotient

end
