module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section

namespace DedekindZetaZeroFree.AdelicSeparation

theorem unitAddTorus_characters_separate {d : Type*}
    (x y : UnitAddTorus d) (hxy : x ≠ y) :
    ∃ χ : AddChar (UnitAddTorus d) Circle, Continuous χ ∧ χ x ≠ χ y := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h
    apply hxy
    funext i
    exact not_not.mp (not_exists.mp h i)
  let χ : AddChar (UnitAddTorus d) Circle :=
    { toFun := fun z => AddCircle.toCircle (z i)
      map_zero_eq_one' := AddCircle.toCircle_zero
      map_add_eq_mul' := fun a b => AddCircle.toCircle_add (a i) (b i) }
  refine ⟨χ, AddCircle.continuous_toCircle.comp (continuous_apply i), ?_⟩
  exact fun h => hi (AddCircle.injective_toCircle one_ne_zero h)

end DedekindZetaZeroFree.AdelicSeparation
