module

public import DedekindZetaZeroFree.LFunctions.Hecke.IdealSeriesAndContinuationWitnesses

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

noncomputable section
open scoped NumberField Classical

def principalUnitRayCharacter (F : Type) [Field F] [NumberField F] :
    DedekindZetaZeroFree.RayClassCharacter F (⊤ : Ideal (𝓞 F)) where
  toFun I := if I = ⊥ then 0 else 1
  map_mul' := by
    intro I J
    by_cases hI : I = ⊥ <;> by_cases hJ : J = ⊥ <;>
      simp [hI, hJ, Ideal.mul_eq_bot]
  map_top' := by
    have h : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := bot_lt_top.ne'
    simp [h]
  eq_zero_iff' := by
    intro I
    by_cases hI : I = ⊥ <;> simp [hI]
  map_span' := by
    intro α hα _ _
    simp [Ideal.span_singleton_eq_bot, hα]

theorem principalUnitRayCharacter_apply (F : Type) [Field F] [NumberField F]
    (I : Ideal (𝓞 F)) :
    principalUnitRayCharacter F I = if I = ⊥ then 0 else 1 := by
  rfl

@[simp] theorem principalUnitRayCharacter_bot (F : Type) [Field F] [NumberField F] :
    principalUnitRayCharacter F ⊥ = 0 := by
  rw [principalUnitRayCharacter_apply]
  simp

@[simp] theorem principalUnitRayCharacter_top (F : Type) [Field F] [NumberField F] :
    principalUnitRayCharacter F ⊤ = 1 := by
  rw [principalUnitRayCharacter_apply]
  simp [bot_lt_top.ne']

theorem principalUnitRayCharacter_isPrincipal (F : Type) [Field F] [NumberField F] :
    (principalUnitRayCharacter F).IsPrincipal := by
  intro I hI _
  rw [principalUnitRayCharacter_apply]
  simp [hI]

theorem principalUnitRayCharacter_isPrimitive (F : Type) [Field F] [NumberField F] :
    (principalUnitRayCharacter F).IsPrimitive := by
  intro 𝔣 h𝔣
  exact absurd h𝔣 (not_lt_of_ge le_top)

theorem exists_principalUnitHeckeWitness
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F) :
    Nonempty (PrincipalHeckeWitness (principalUnitRayCharacter F)) :=
  exists_principalHeckeWitness hF (f := ⊤) bot_lt_top.ne'
    (principalUnitRayCharacter F) (principalUnitRayCharacter_isPrimitive F)
    (principalUnitRayCharacter_isPrincipal F)

end

end DedekindZetaZeroFree.LargeSieve
