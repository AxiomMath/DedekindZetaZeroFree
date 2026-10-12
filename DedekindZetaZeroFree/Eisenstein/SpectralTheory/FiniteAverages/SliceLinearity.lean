module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteAverages.SliceIntegrability

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualFiniteAnchor
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable (V : Level F ζ hζ)

theorem anchorAverage_sum_of_slices (dk : Measure (KPMsGreenFlux.K F)) [IsFiniteMeasure dk]
    {ι : Type*} [Fintype ι] (a : ι → ℂ) (φ : ι → G F ζ hζ → ℂ)
    (hφ : ∀i j, Continuous (fun k : KPMsGreenFlux.K F =>
      φ i (KPMsGreenFlux.compactInsertion F ζ hζ k *
        (KPBoundedCuspFrames.actualFiniteRepresentative
          (nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V) j).val))) (ω) :
    anchorAverage (R:=R) (P:=P) V dk (fun g => ∑i, a i * φ i g) ω =
      ∑i, a i * anchorAverage (R:=R) (P:=P) V dk (φ i) ω := by
  let : CompactSpace KPCplxPrincipalSeriesCharts.compactSubgroup :=
    isCompact_iff_compactSpace.mp KPCplxPrincipalSeriesCharts.compactSubgroup_isCompact
  unfold anchorAverage
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro i hi
    exact ((hφ i ω.1).const_mul (a i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem anchorIntegral_sum_of_slices (dk : Measure (KPMsGreenFlux.K F)) [IsFiniteMeasure dk]
    {ι : Type*} [Fintype ι] (a : ι → ℂ) (φ : ι → G F ζ hζ → ℂ)
    (hφ : ∀i j, Continuous (fun k : KPMsGreenFlux.K F =>
      φ i (KPMsGreenFlux.compactInsertion F ζ hζ k *
        (KPBoundedCuspFrames.actualFiniteRepresentative
          (nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V) j).val))) :
    (∫ω, anchorAverage (R:=R) (P:=P) V dk (fun g => ∑i, a i * φ i g) ω
      ∂(nativeDisintegration F ζ hζ R P (nativeRecipe F ζ hζ R P) V).beta) =
      ∑i, a i * ∫ω, anchorAverage (R:=R) (P:=P) V dk (φ i) ω
        ∂(nativeDisintegration F ζ hζ R P (nativeRecipe F ζ hζ R P) V).beta := by
  simp_rw [anchorAverage_sum_of_slices V dk a φ hφ]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro i hi
    exact (anchorAverage_integrable_of_slices V (φ i) (hφ i) dk).const_mul (a i)

end DedekindZetaZeroFree.FourierContinuation.ResidualFiniteAnchor

end
