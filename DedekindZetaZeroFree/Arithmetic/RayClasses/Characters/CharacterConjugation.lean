module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped NumberField

variable {F : Type} [Field F] [NumberField F] {m : Ideal (𝓞 F)}

def conjugateRayCharacter (η : DedekindZetaZeroFree.RayClassCharacter F m) :
    DedekindZetaZeroFree.RayClassCharacter F m where
  toFun I := (starRingEnd ℂ) (η I)
  map_mul' := by
    intro I J
    simp only [η.map_mul', map_mul]
  map_top' := by
    simp only [η.map_top', map_one]
  eq_zero_iff' := by
    intro I
    simpa using η.eq_zero_iff' I
  map_span' := by
    intro α hα hm hpos
    simp only [η.map_span' α hα hm hpos, map_one]

@[simp] theorem conjugateRayCharacter_apply
    (η : DedekindZetaZeroFree.RayClassCharacter F m) (I : Ideal (𝓞 F)) :
    conjugateRayCharacter η I = (starRingEnd ℂ) (η I) := by
  rfl

@[simp] theorem conjugateRayCharacter_isPrimitive_iff
    (η : DedekindZetaZeroFree.RayClassCharacter F m) :
    (conjugateRayCharacter η).IsPrimitive ↔ η.IsPrimitive := by
  simp [DedekindZetaZeroFree.RayClassCharacter.IsPrimitive,
    map_eq_one_iff (starRingEnd ℂ) (star_injective)]

@[simp] theorem conjugateRayCharacter_isPrincipal_iff
    (η : DedekindZetaZeroFree.RayClassCharacter F m) :
    (conjugateRayCharacter η).IsPrincipal ↔ η.IsPrincipal := by
  simp [DedekindZetaZeroFree.RayClassCharacter.IsPrincipal,
    map_eq_one_iff (starRingEnd ℂ) (star_injective)]

@[simp] theorem rayClassCharacter_apply_bot
    (η : DedekindZetaZeroFree.RayClassCharacter F m) : η ⊥ = 0 := by
  exact (η.eq_zero_iff' ⊥).mpr (Or.inl rfl)

end

end DedekindZetaZeroFree.Hecke
