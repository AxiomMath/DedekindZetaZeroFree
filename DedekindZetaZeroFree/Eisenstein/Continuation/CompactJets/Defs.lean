module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestFriedrichsRealization

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

open KPContSectorSmoothFramesSupport KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

def ChartHolomorphicOn (a : ActualChart (U := U) (H := H))
    (w : ℂ → Sections F ζ hζ U R P H) (O : Set ℂ) : Prop :=
  ∀ (C : Set (M F)) (hC : IsCompact C), C ⊆ omega a →
    ∀ (n : ℕ) (v : Fin n → M F),
      letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
      ∃ j : ℂ → ContinuousMap C ℂ, DifferentiableOn ℂ j O ∧
        ∀ s ∈ O, ∀ x : C, j s x =
          iteratedFDerivWithin ℝ n ((isotropyChart a).coefficient (w s))
            (omega a) x.val v

def Represents (V : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (w : Sections F ζ hζ U R P H) : Prop :=
  (V : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) =ᵐ[coveredMeasure F ζ hζ R U]
    (scalarRepresentative F ζ hζ U R P H w).val ∧
  ∃ b : BorelL2Sections F ζ hζ U R P H,
    b.val = w ∧ toSector F ζ hζ U R P H b = V

def Conclusions (w : ℂ → Sections F ζ hζ U R P H) (O : Set ℂ)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) : Prop :=
  ∃ wk : ℕ → ℂ → Sections F ζ hζ U R P H,
  ∃ W : ℕ → ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U,
    (∀ s ∈ O, wk 0 s = w s) ∧
    (∀ k s, s ∈ O → IsSmoothSections F ζ hζ U R P H (wk k s) ∧
      tsupport (sectionNorm F ζ hζ U R P H (wk k s)) ⊆ K) ∧
    (∀ k s, s ∈ O → ∀ i x,
      (wk k s i).val x = iteratedDerivWithin k (fun z => (w z i).val x) O s) ∧
    (∀ k s, s ∈ O → Represents (W k s) (wk k s) ∧
      ∀ V : KPContSectorClosedLpSubspace.H F ζ hζ R U,
        Represents V (wk k s) → V = W k s) ∧
    (∀ k, DifferentiableOn ℂ (W k) O) ∧
    (∀ k s, s ∈ O → iteratedDerivWithin k (W 0) O s = W k s) ∧
    (∀ k (L : Set ℂ), IsCompact L → L ⊆ O →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L, ‖W k s‖ ≤ B) ∧
    (∀ k s, s ∈ O → ∀ a : ActualChart (U := U) (H := H),
      (fun y : a.domain => (isotropyChart a).coefficient (wk k s)
        (KPContActualCotangentPieceHilbertSum.coordinates a y).val) =ᵐ[a.liftedMeasure]
      (fun y : a.domain => iteratedDerivWithin k
        (fun z => (isotropyChart a).coefficient (w z)
          (KPContActualCotangentPieceHilbertSum.coordinates a y).val) O s)) ∧
    (∀ k s, s ∈ O →
      (W k s : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) =ᵐ[coveredMeasure F ζ hζ R U]
      (fun x => iteratedDerivWithin k
        (fun z => (scalarRepresentative F ζ hζ U R P H (w z)).val x) O s))

def IsLocalLaplacianFamily (w v : ℂ → Sections F ζ hζ U R P H)
    (O : Set ℂ) : Prop :=
  ∀ s ∈ O, ∀ a : ActualChart (U := U) (H := H), ∀ x : omega a,
    (isotropyChart a).coefficient (v s) x.val =
      HyperbolicChart.laplacian (d F)
        (liftExtension a (sectionFields (w s) a)) x.val

end DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

end
