module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.TwelfthRootNonvanishing
public import DedekindZetaZeroFree.Nonvanishing.Descent.AbelianZeroTransfer
public import DedekindZetaZeroFree.Arithmetic.Kummer.TwelfthCyclotomicExtension

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative

open DedekindZetaZeroFree

theorem dedekindZeta_ne_zero (K : Type) [Field K] [NumberField K] :
    ∃ f : Complex → Complex,
      DifferentiableOn Complex f (({1} : Set Complex)ᶜ) ∧
      (∀ s : Complex, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
      ∀ s : Complex, 31 / 32 < s.re → s ≠ 1 → f s ≠ 0 := by
  obtain ⟨hGal, hcomm, hTC, hζ⟩ := cyclotomic12_context K
  obtain ⟨fF, hfF, hagF, hnzF⟩ :=
    mu12_continuation_ne_zero (CyclotomicField 12 K) hTC ⟨hζ.choose, hζ.choose_spec.1⟩
  exact dedekindZeta_zeroFree_of_abelian_extension K (CyclotomicField 12 K)
    hcomm (31 / 32) fF hfF hagF hnzF

end DedekindZetaZeroFree.Quantitative
