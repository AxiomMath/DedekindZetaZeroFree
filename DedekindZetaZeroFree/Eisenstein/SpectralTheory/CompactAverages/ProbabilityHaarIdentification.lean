module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactAverages.ArchimedeanReduction

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualCompactAverageProjection
open KPContSectorCoveredQuotientVocabulary KPMsGreenFlux
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming K_U_compact → K_U_compact
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : CompactOpenLevel (FiniteCover F ζ hζ))
local instance : MeasurableSpace (K_U F ζ hζ U) := borel _
local instance : BorelSpace (K_U F ζ hζ U) := ⟨rfl⟩
local instance : CompactSpace (K_U F ζ hζ U) := isCompact_iff_compactSpace.mp (K_U_compact F ζ hζ U)

theorem probability_isHaar (μ : Measure (K_U F ζ hζ U))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] : μ.IsHaarMeasure := by
  apply Measure.isHaarMeasure_of_isCompact_nonempty_interior μ Set.univ isCompact_univ
  · simp
  · simp
  · simp

theorem probability_average_eq_arch
    (μ : Measure (K_U F ζ hζ U)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ν : Measure (K F)) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (φ : ActualCover F ζ hζ → ℂ) (hφ : Continuous φ)
    (hU : ∀ (g : ActualCover F ζ hζ) (c : FiniteCover F ζ hζ), c ∈ U.toOpenSubgroup →
      φ (g * c.val) = φ g) (g : ActualCover F ζ hζ) :
    (∫k : K_U F ζ hζ U, φ (g * k.val) ∂μ) =
      ∫k : K F, φ (g * compactInsertion F ζ hζ k) ∂ν := by
  letI := probability_isHaar F ζ hζ U μ
  exact average_eq_arch F ζ hζ U μ ν φ hφ hU g
end DedekindZetaZeroFree.FourierContinuation.ResidualCompactAverageProjection

end
