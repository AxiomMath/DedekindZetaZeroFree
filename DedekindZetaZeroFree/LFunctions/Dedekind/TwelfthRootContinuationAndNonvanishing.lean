module

public import DedekindZetaZeroFree.LFunctions.Dedekind.AbelianContinuation
public import DedekindZetaZeroFree.LFunctions.Dedekind.TwelfthRootPointwiseNonvanishing

@[expose] public section

namespace DedekindZetaZeroFree

theorem principal_mu12_dedekindZeta_ne_zero
    (F : Type) [Field F] [NumberField F]
    (htc : NumberField.IsTotallyComplex F) (hmu : ∃ ζ : F, IsPrimitiveRoot ζ 12) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta F s) ∧
      ∀ s : ℂ, 5999 / 6000 < s.re → s ≠ 1 → f s ≠ 0 := by
  obtain ⟨f, hf, hmatch⟩ := dedekindZeta_continuation F
  exact ⟨f, hf, hmatch,
    principal_mu12_continuation_ne_zero F htc hmu f hf hmatch⟩

end DedekindZetaZeroFree
