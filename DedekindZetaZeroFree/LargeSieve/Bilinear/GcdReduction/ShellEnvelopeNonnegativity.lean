module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.GcdTailAndMaskedShellBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.LargeSieve.Sieve.GcdReduction
open scoped NumberField Classical

theorem envelope_nonneg
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (hW : SieveWeight W)
    (M X K : ℝ) (hM : 1 ≤ M) (hX : 1 ≤ X) (hK : 0 < K) :
    0 ≤ B2env F c Q W M X K := by
  unfold B2env
  exact Real.sSup_nonneg' ⟨0, Or.inl (Or.inl rfl), le_rfl⟩

end DedekindZetaZeroFree.LargeSieve.Sieve.GcdReduction

end
