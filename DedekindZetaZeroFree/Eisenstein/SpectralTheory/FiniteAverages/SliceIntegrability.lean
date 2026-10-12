module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteAverages.AnchorIntegrability

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

theorem anchorAverage_integrable_of_slices (φ : G F ζ hζ → ℂ) (hφ : ∀j, Continuous (fun k : KPMsGreenFlux.K F =>
      φ (KPMsGreenFlux.compactInsertion F ζ hζ k *
        (KPBoundedCuspFrames.actualFiniteRepresentative
          (nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V) j).val)))
    (dk : Measure (KPMsGreenFlux.K F)) [IsFiniteMeasure dk] :
    Integrable (anchorAverage (R:=R) (P:=P) V dk φ)
      (nativeDisintegration F ζ hζ R P (nativeRecipe F ζ hζ R P) V).beta := by
  let A := nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V
  let J := KPMsFixedHaarDisintegration.CuspIndex A
  letI : TopologicalSpace J := ⊥
  letI : DiscreteTopology J := ⟨rfl⟩
  letI : CompactSpace KPCplxPrincipalSeriesCharts.compactSubgroup :=
    isCompact_iff_compactSpace.mp KPCplxPrincipalSeriesCharts.compactSubgroup_isCompact
  letI := (nativeDisintegration F ζ hζ R P (nativeRecipe F ζ hζ R P) V).finite_beta
  let H : J × KPMsGreenFlux.K F → ℂ := fun z =>
    φ (KPMsGreenFlux.compactInsertion F ζ hζ z.2 *
      (KPBoundedCuspFrames.actualFiniteRepresentative A z.1).val)
  have hc : Continuous H := by
    apply continuous_prod_of_discrete_left.mpr
    intro j
    exact hφ j
  obtain ⟨b,hb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (J × KPMsGreenFlux.K F))).bddAbove_image hc.norm.continuousOn
  have hp : Continuous (fun ω : KPMsFixedHaarDisintegration.Omega A => (ω.1 : J)) :=
    continuous_sigma (fun _ => continuous_const)
  have hi : Integrable (fun z : KPMsFixedHaarDisintegration.Omega A × KPMsGreenFlux.K F => H (z.1.1,z.2))
      ((nativeDisintegration F ζ hζ R P (nativeRecipe F ζ hζ R P) V).beta.prod dk) := by
    apply Integrable.of_bound (hc.comp ((hp.comp continuous_fst).prodMk continuous_snd)).aestronglyMeasurable b
    exact Filter.Eventually.of_forall (fun z => hb ⟨(z.1.1,z.2),Set.mem_univ _,rfl⟩)
  exact hi.integral_prod_left

end DedekindZetaZeroFree.FourierContinuation.ResidualFiniteAnchor

end
