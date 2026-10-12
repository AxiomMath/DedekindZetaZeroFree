module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F] {m : Ideal (𝓞 F)}

theorem primitivePrincipal_modulus_eq_top
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (hprimitive : η.IsPrimitive) (hprincipal : η.IsPrincipal) :
    m = ⊤ := by
  by_contra hm
  have hlt : m < ⊤ := lt_top_iff_ne_top.mpr hm
  obtain ⟨α, hα0, _hα1, _hpos, hspan, hne⟩ := hprimitive ⊤ hlt
  have hspanne : Ideal.span {α} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hα0
  exact hne (hprincipal _ hspanne hspan)

theorem primitivePrincipal_apply_nonzero
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (hprimitive : η.IsPrimitive) (hprincipal : η.IsPrincipal)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) : η I = 1 := by
  have hm : m = ⊤ := primitivePrincipal_modulus_eq_top η hprimitive hprincipal
  exact hprincipal I hI (by rw [hm, sup_top_eq])

theorem primitivePrincipal_apply_eq_ite
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (hprimitive : η.IsPrimitive) (hprincipal : η.IsPrincipal)
    (I : Ideal (𝓞 F)) : η I = if I = ⊥ then 0 else 1 := by
  by_cases hI : I = ⊥
  · rw [if_pos hI, hI]
    exact (η.eq_zero_iff' ⊥).mpr (Or.inl rfl)
  · rw [if_neg hI]
    exact primitivePrincipal_apply_nonzero η hprimitive hprincipal I hI

end

end DedekindZetaZeroFree.Hecke
