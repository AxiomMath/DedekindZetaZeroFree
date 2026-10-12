module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.BandlimitedPoissonGramMajorant

@[expose] public section

namespace DedekindZetaZeroFree.ProbeAdditiveGramBounds
noncomputable section
open scoped Classical NumberField ComplexConjugate
open IsDedekindDomain NumberField

theorem trace_phase_continuous
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (χ : SLocalProduct F S → ℂ)
    (hχ : ∀ x, χ x =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((∑ v : InfinitePlace F, 2 *
          (InfinitePlace.Completion.extensionEmbedding v (x.1 v)).re) : ℂ)) *
        ∏ v : S, (e v (x.2 v) : ℂ)) : Continuous χ := by
  have hfun : χ = fun x =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((∑ v : InfinitePlace F, 2 *
          (InfinitePlace.Completion.extensionEmbedding v (x.1 v)).re) : ℂ)) *
        ∏ v : S, (e v (x.2 v) : ℂ) := funext hχ
  rw [hfun]
  have harch (v : InfinitePlace F) :
      Continuous (fun x : SLocalProduct F S =>
        InfinitePlace.Completion.extensionEmbedding v (x.1 v)) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp
      ((continuous_apply v).comp continuous_fst)
  fun_prop

end
end DedekindZetaZeroFree.ProbeAdditiveGramBounds
