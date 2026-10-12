module

public import DedekindZetaZeroFree.Nonvanishing.Descent.TwelfthRootExtension
public import DedekindZetaZeroFree.LFunctions.Dedekind.TwelfthRootContinuationAndNonvanishing

@[expose] public section

namespace DedekindZetaZeroFree

theorem dedekindZeta_ne_zero
    (K : Type) [Field K] [NumberField K] :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
      ∀ s : ℂ, 5999 / 6000 < s.re → s ≠ 1 → f s ≠ 0 := by
  exact dedekindZeta_ne_zero_of_mu12
    (fun F _ _ htc hmu => principal_mu12_dedekindZeta_ne_zero F htc hmu) K

end DedekindZetaZeroFree
