module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactAverages.ArchimedeanProjection

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualCompactAverageProjection
open KPContSectorCoveredQuotientVocabulary KPMsGreenFlux
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming productEquiv → productEquiv
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming productEquiv_apply → productEquiv_apply
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : CompactOpenLevel (FiniteCover F ζ hζ))
local instance : MeasurableSpace (K_U F ζ hζ U) := borel _
local instance : BorelSpace (K_U F ζ hζ U) := ⟨rfl⟩

theorem split_eq (k : K_U F ζ hζ U) :
    k.val = compactInsertion F ζ hζ (archProjection F ζ hζ U k) *
      (((productEquiv F ζ hζ).symm k.val).2).val := by
  have he := productEquiv_apply F ζ hζ ((productEquiv F ζ hζ).symm k.val).1
    ((productEquiv F ζ hζ).symm k.val).2
  rw [Prod.mk.eta,ContinuousMulEquiv.apply_symm_apply] at he
  exact he

theorem average_eq_arch
    (μ : Measure (K_U F ζ hζ U)) [IsProbabilityMeasure μ] [μ.IsHaarMeasure]
    (ν : Measure (K F)) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (φ : ActualCover F ζ hζ → ℂ) (hφ : Continuous φ)
    (hU : ∀ (g : ActualCover F ζ hζ) (c : FiniteCover F ζ hζ), c ∈ U.toOpenSubgroup →
      φ (g * c.val) = φ g) (g : ActualCover F ζ hζ) :
    (∫k : K_U F ζ hζ U, φ (g * k.val) ∂μ) =
      ∫k : K F, φ (g * compactInsertion F ζ hζ k) ∂ν := by
  have hi (k : K F) : compactInsertion F ζ hζ k =
      productEquiv F ζ hζ ((fun w => (k w).val),1) := by
    rw [productEquiv_apply]
    simp [compactInsertion]
  have hp : Continuous (fun k : K F => productEquiv F ζ hζ ((fun w => (k w).val),1)) :=
    (productEquiv F ζ hζ).continuous.comp
      ((continuous_pi fun w => continuous_subtype_val.comp (continuous_apply w)).prodMk continuous_const)
  have hins : Continuous (fun k : K F => compactInsertion F ζ hζ k) :=
    hp.congr (fun k => (hi k).symm)
  have hc : Continuous (fun k : K F => φ (g * compactInsertion F ζ hζ k)) :=
    hφ.comp (continuous_const.mul hins)
  have he := integral_map (μ := μ) (archProjection_continuous F ζ hζ U).measurable.aemeasurable
    hc.aestronglyMeasurable
  rw [(archProjection_measurePreserving F ζ hζ U μ ν).map_eq] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [] with k
  rw [split_eq F ζ hζ U k,←mul_assoc]
  exact hU _ _ (split_mem F ζ hζ U k).2

end DedekindZetaZeroFree.FourierContinuation.ResidualCompactAverageProjection

end
