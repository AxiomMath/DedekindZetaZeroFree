module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.DedekindZetaNonvanishing

@[expose] public section

namespace DedekindZetaZeroFree

theorem dedekindZeta_ne_zero
    (K : Type) [Field K] [NumberField K] :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
      ∀ s : ℂ, 31 / 32 < s.re → s ≠ 1 → f s ≠ 0 := by
  exact DedekindZetaZeroFree.Quantitative.dedekindZeta_ne_zero K

end DedekindZetaZeroFree
