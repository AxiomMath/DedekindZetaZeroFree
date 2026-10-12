module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

@[simp]
theorem nonzero_bottom_multiples_eq_empty (F : Type*) [Field F] [NumberField F] :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (⊥ : Ideal (𝓞 F)) ∣ I} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro I ⟨hI, hdvd⟩
  exact hI (zero_dvd_iff.mp hdvd)

end DedekindZetaZeroFree.LargeSieve
