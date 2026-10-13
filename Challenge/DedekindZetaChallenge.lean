module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section

namespace DedekindZetaZeroFree

theorem main (K : Type) [Field K] [NumberField K] : ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
      ∀ s, 31 / 32 < s.re → s ≠ 1 → f s ≠ 0 := by sorry

end DedekindZetaZeroFree
