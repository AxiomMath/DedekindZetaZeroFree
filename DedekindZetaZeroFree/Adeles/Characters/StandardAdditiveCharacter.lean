module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.PlacesAndCompletions
public import DedekindZetaZeroFree.Adeles.Characters.RationalFrequencyNontriviality

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.PrincipalOfKP

def standardCharacter (F : Type) [Field F] [NumberField F] :
    ContinuousAddChar (KPAdditiveQuotient F) where
  toFun x := (adelicTraceQuotientCharacter F x : ℂ)
  map_zero_eq_one' := by
    change ((adelicTraceQuotientCharacter F 0 : Circle) : ℂ) = 1
    rw [AddChar.map_zero_eq_one (adelicTraceQuotientCharacter F), Circle.coe_one]
  map_add_eq_mul' := by
    intro a b
    change ((adelicTraceQuotientCharacter F (a + b) : Circle) : ℂ) =
      (adelicTraceQuotientCharacter F a : ℂ) * (adelicTraceQuotientCharacter F b : ℂ)
    rw [AddChar.map_add_eq_mul (adelicTraceQuotientCharacter F) a b, Circle.coe_mul]
  continuous_toFun :=
    continuous_subtype_val.comp (continuous_adelicTraceQuotientCharacter F)
  unitary := fun a => Circle.norm_coe _

theorem standardCharacter_nontrivial (F : Type) [Field F] [NumberField F] :
    KPReflectionSpec.NontrivialCharacter (standardCharacter F) := by
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.1 (adelicTraceQuotientCharacter_ne_one F)
  refine ⟨x, ?_⟩
  intro h
  change ((adelicTraceQuotientCharacter F x : Circle) : ℂ) = 1 at h
  apply hx
  apply Subtype.ext
  rw [h, Circle.coe_one]

end DedekindZetaZeroFree.PrincipalOfKP

end
