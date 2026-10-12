module

public import DedekindZetaZeroFree.LFunctions.Dedekind.MixedThetaPairMellin

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

theorem zeta_mixedThetaModel (K : Type) [Field K] [NumberField K] :
    ∃ P : WeakFEPair ℂ, P.k = 1 ∧
      ∀ s : ℂ, 1 < s.re →
        HasMellin (fun t : ℝ => P.f t - P.f₀) s
          (zetaGammaFactor K s * NumberField.dedekindZeta K s) := by
  refine ⟨Theta.mixedThetaPair K, Theta.mixedThetaPair_k K, ?_⟩
  intro s hs
  exact Theta.hasMellin_mixedThetaPair K hs

end DedekindZetaZeroFree.AbelianQuotient
