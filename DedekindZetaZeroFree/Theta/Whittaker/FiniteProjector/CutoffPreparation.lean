module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.Data

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources ThetaExpansion
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}

theorem prepare_cutoffs {N : TraceHaarTransport R}
    (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R) :
    ∃ C : FirstRootCutoffs R,
      C.exponent = B.exponent ∧
      (∀ p, C.cutoff p ≤ B.cutoff p) ∧
      (∀ p, (C.cutoff p : Set _) ⊆ A.neighborhood p) ∧
      ∀ v y,
        (if ∀ p : R.A.Sf, y.2 p ∈ C.cutoff p then (1 : ℂ) else 0) *
          MomentSources.fourier R A.base.sources.dq (A.base.realization.theta v) (diagonal R y) =
        firstRootRadialProfile R C y := by
  obtain ⟨C, he, hle, hsub⟩ := B.shrink A.neighborhood
    A.open_neighborhood A.one_neighborhood
  refine ⟨C, he, hle, hsub, ?_⟩
  intro v y
  by_cases hy : ∀ p : R.A.Sf, y.2 p ∈ C.cutoff p
  · rw [if_pos hy, A.spherical_near v y (fun p => hsub p (hy p))]
    rw [firstRootRadialProfile, if_pos hy]
  · simp only [if_neg hy, zero_mul, firstRootRadialProfile]

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
