module

public import DedekindZetaZeroFree.Nonvanishing.Descent.AbelianZeroTransfer
public import DedekindZetaZeroFree.Arithmetic.Kummer.TwelfthCyclotomicExtension

@[expose] public section

namespace DedekindZetaZeroFree

theorem dedekindZeta_ne_zero_of_mu12
    (hlarge : ∀ (F : Type) [Field F] [NumberField F],
      NumberField.IsTotallyComplex F → (∃ ζ : F, IsPrimitiveRoot ζ 12) →
      ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
        (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta F s) ∧
        ∀ s : ℂ, 5999 / 6000 < s.re → s ≠ 1 → f s ≠ 0)
    (K : Type) [Field K] [NumberField K] :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
      ∀ s : ℂ, 5999 / 6000 < s.re → s ≠ 1 → f s ≠ 0 := by
  obtain ⟨hGal, hcomm, hTC, hζ⟩ := cyclotomic12_context K
  obtain ⟨fF, hfF, hagF, hnzF⟩ :=
    hlarge (CyclotomicField 12 K) hTC ⟨hζ.choose, hζ.choose_spec.1⟩
  exact dedekindZeta_zeroFree_of_abelian_extension K (CyclotomicField 12 K)
    hcomm (5999 / 6000) fF hfF hagF hnzF

end DedekindZetaZeroFree
