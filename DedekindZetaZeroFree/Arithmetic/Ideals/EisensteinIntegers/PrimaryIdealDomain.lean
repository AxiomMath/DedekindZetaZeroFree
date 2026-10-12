module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Three

@[expose] public section

namespace DedekindZetaZeroFree.Eisenstein

attribute [local instance] IsCyclotomicExtension.Rat.three_pid

abbrev R (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] := NumberField.RingOfIntegers E

noncomputable abbrev η (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E]
    (ω : E) (hω : IsPrimitiveRoot ω 3) : R E := hω.toInteger

noncomputable abbrev «λ» (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E]
    (ω : E) (hω : IsPrimitiveRoot ω 3) : R E := η E ω hω - 1

def m3 (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] : Ideal (R E) :=
  Ideal.span {(3 : R E)}

abbrev red3 (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] :
    R E →+* (R E ⧸ m3 E) := Ideal.Quotient.mk (m3 E)

abbrev ιR (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ι : E →+* ℂ) : R E →+* ℂ :=
  ι.comp (algebraMap (R E) E)

def I3 (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] : Submonoid (Ideal (R E)) where
  carrier := {A | A ≠ ⊥ ∧ A ⊔ m3 E = ⊤}
  one_mem' := by simp
  mul_mem' := by
    rintro A B ⟨hA, hA3⟩ ⟨hB, hB3⟩
    refine ⟨?_, ?_⟩
    · simpa only [Ne, Ideal.mul_eq_bot, not_or] using And.intro hA hB
    · exact Ideal.isCoprime_iff_sup_eq.mp
        ((Ideal.isCoprime_iff_sup_eq.mpr hA3).mul_left
          (Ideal.isCoprime_iff_sup_eq.mpr hB3))

@[simp] theorem mem_I3 (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (A : Ideal (R E)) :
    A ∈ I3 E ↔ A ≠ ⊥ ∧ A ⊔ m3 E = ⊤ := Iff.rfl

end DedekindZetaZeroFree.Eisenstein
