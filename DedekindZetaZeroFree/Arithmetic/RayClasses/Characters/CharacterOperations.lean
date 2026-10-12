module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.RayOperations

open scoped NumberField Classical
open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]

def conjugate {m : Ideal (𝓞 F)} (η : RayClassCharacter F m) : RayClassCharacter F m where
  toFun I := (starRingEnd ℂ) (η I)
  map_mul' := fun I J => by simp only [η.map_mul' I J, map_mul]
  map_top' := by simp only [η.map_top', map_one]
  eq_zero_iff' := fun I => by simp only [starRingEnd_apply, star_eq_zero, η.eq_zero_iff' I]
  map_span' := fun α hα hmem hpos => by simp only [η.map_span' α hα hmem hpos, map_one]

def mul {m f : Ideal (𝓞 F)} (η : RayClassCharacter F m)
    (θ : RayClassCharacter F f) : RayClassCharacter F (m * f) where
  toFun I := η I * θ I
  map_mul' := fun I J => by rw [η.map_mul' I J, θ.map_mul' I J]; ring
  map_top' := by rw [η.map_top', θ.map_top', mul_one]
  eq_zero_iff' := fun I => by
    have h : I ⊔ (m * f) = ⊤ ↔ I ⊔ m = ⊤ ∧ I ⊔ f = ⊤ := by
      constructor
      · intro h
        exact ⟨top_unique (le_trans (le_of_eq h.symm) (sup_le_sup_left Ideal.mul_le_left I)),
          top_unique (le_trans (le_of_eq h.symm) (sup_le_sup_left Ideal.mul_le_right I))⟩
      · rintro ⟨h1, h2⟩; rw [Ideal.sup_mul_eq_of_coprime_left h1, h2]
    have hor : ((I = ⊥ ∨ ¬ I ⊔ m = ⊤) ∨ (I = ⊥ ∨ ¬ I ⊔ f = ⊤)) ↔
        (I = ⊥ ∨ ¬ I ⊔ (m * f) = ⊤) := by rw [h]; tauto
    simp only [mul_eq_zero, η.eq_zero_iff' I, θ.eq_zero_iff' I, ne_eq]
    exact hor
  map_span' := fun α hα hmem hpos => by
    rw [η.map_span' α hα (Ideal.mul_le_left (I := m) (J := f) hmem) hpos,
      θ.map_span' α hα (Ideal.mul_le_right (I := m) (J := f) hmem) hpos, mul_one]

@[simp] theorem conjugate_apply {m : Ideal (𝓞 F)} (η : RayClassCharacter F m)
    (I : Ideal (𝓞 F)) : conjugate η I = (starRingEnd ℂ) (η I) := rfl

@[simp] theorem mul_apply {m f : Ideal (𝓞 F)} (η : RayClassCharacter F m)
    (θ : RayClassCharacter F f) (I : Ideal (𝓞 F)) :
    mul η θ I = η I * θ I := rfl

theorem modulus_eq_top_of_primitive_principal {m : Ideal (𝓞 F)}
    (η : RayClassCharacter F m) (hprim : η.IsPrimitive) (hprincipal : η.IsPrincipal) :
    m = ⊤ := by
  by_contra hm
  have hlt : m < ⊤ := lt_of_le_of_ne le_top hm
  obtain ⟨α, hα, _hmem, _hpos, hspan, hne⟩ := hprim ⊤ hlt
  exact hne (hprincipal _ (fun hbot => hα (Ideal.span_singleton_eq_bot.mp hbot)) hspan)

theorem map_mul {m : Ideal (𝓞 F)} (η : RayClassCharacter F m)
    (I J : Ideal (𝓞 F)) : η (I * J) = η I * η J := η.map_mul' I J

theorem map_top {m : Ideal (𝓞 F)} (η : RayClassCharacter F m) : η ⊤ = 1 := η.map_top'

theorem eq_zero_iff {m : Ideal (𝓞 F)} (η : RayClassCharacter F m)
    (I : Ideal (𝓞 F)) : η I = 0 ↔ I = ⊥ ∨ I ⊔ m ≠ ⊤ := η.eq_zero_iff' I

theorem map_bot {m : Ideal (𝓞 F)} (η : RayClassCharacter F m) : η ⊥ = 0 := by
  rw [eq_zero_iff]; exact Or.inl rfl

theorem ne_zero_iff {m : Ideal (𝓞 F)} (η : RayClassCharacter F m)
    (I : Ideal (𝓞 F)) : η I ≠ 0 ↔ I ≠ ⊥ ∧ I ⊔ m = ⊤ := by
  rw [ne_eq, eq_zero_iff]; tauto

end DedekindZetaZeroFree.LargeSieve.RayOperations
