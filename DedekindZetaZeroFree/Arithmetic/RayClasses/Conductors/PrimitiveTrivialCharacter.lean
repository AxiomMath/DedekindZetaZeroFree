module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMu12Pointwise

open scoped NumberField

theorem principal_primitive_top_character_exists
    (F : Type) [Field F] [NumberField F] :
    ∃ η : RayClassCharacter F ⊤, η.IsPrincipal ∧ η.IsPrimitive := by
  refine ⟨{ toFun := fun I => if I = ⊥ then 0 else 1
            map_mul' := ?_
            map_top' := ?_
            eq_zero_iff' := ?_
            map_span' := ?_ }, ?_, ?_⟩
  · intro I J
    by_cases hI : I = ⊥
    · simp [hI]
    by_cases hJ : J = ⊥
    · simp [hJ]
    simp [hI, hJ, Ideal.mul_eq_bot]
  · simp
  · intro I
    simp
  · intro α hα _ _
    simp [Ideal.span_singleton_eq_bot, hα]
  · intro I hI _
    simp [hI]
  · intro 𝔣 h𝔣
    exact absurd h𝔣 (not_lt_of_ge le_top)

end DedekindZetaZeroFree.PrincipalMu12Pointwise
