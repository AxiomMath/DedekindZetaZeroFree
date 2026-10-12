module

public import DedekindZetaZeroFree.Arithmetic.Kummer.FrequencyClassesAndCharacterRigidity

@[expose] public section

open scoped NumberField
open IsDedekindDomain

namespace DedekindZetaZeroFree.Detector.FrequencyPrincipal

variable {F : Type} [Field F] [NumberField F]

noncomputable def principalRay : RayClassCharacter F ⊤ where
  toFun n := if n = ⊥ then 0 else 1
  map_mul' I J := by
    classical
    by_cases hI : I = ⊥ <;> by_cases hJ : J = ⊥ <;> simp [hI, hJ]
  map_top' := by simp
  eq_zero_iff' n := by
    classical
    by_cases hn : n = ⊥ <;> simp [hn]
  map_span' a ha hc hp := by
    have hn : Ideal.span {a} ≠ (⊥ : Ideal (𝓞 F)) := by
      intro h
      have hh : a ∈ (⊥ : Ideal (𝓞 F)) := h ▸ Ideal.subset_span (by simp)
      exact ha (by simpa using hh)
    simp [hn]

noncomputable def principalPrimitive : PrimitiveFrequencyCharacter F where
  conductor := ⊤
  conductor_ne_zero := top_ne_bot
  character := principalRay
  primitive := by intro 𝔣 hf; exact (not_lt_of_ge le_top hf).elim

theorem principalPrimitive_principal :
    (principalPrimitive (F := F)).character.IsPrincipal := by
  intro n hn hc
  simp [principalPrimitive, principalRay, hn]

end DedekindZetaZeroFree.Detector.FrequencyPrincipal
