module

public import DedekindZetaZeroFree.LFunctions.Dedekind.EntireAbelianQuotient

@[expose] public section

namespace DedekindZetaZeroFree

theorem dedekindZeta_continuation
    (K : Type) [Field K] [NumberField K] :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      ∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s := by

  obtain ⟨fK, _fL, _g, hfK, _hfL, _hg, hagK, _hagL, _hquot⟩ :=
    DedekindZetaZeroFree.dedekindAbelianQuotient K K (fun σ τ => Subsingleton.elim (σ * τ) (τ * σ))
  exact ⟨fK, hfK, hagK⟩

end DedekindZetaZeroFree
