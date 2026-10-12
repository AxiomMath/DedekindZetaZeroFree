module

public import DedekindZetaZeroFree.Main

@[expose] public section

namespace DedekindZetaZeroFree

theorem main (K : Type) [Field K] [NumberField K] : ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
      ∀ s, (5999 : ℝ) / 6000 < s.re → s ≠ 1 → f s ≠ 0 := by
  exact DedekindZetaZeroFree.dedekindZeta_ne_zero K

end DedekindZetaZeroFree
