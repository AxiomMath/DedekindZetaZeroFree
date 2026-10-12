module

public import DedekindZetaZeroFree.Theta.Periods.Cusps.ShapeMeasureTransport
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.BoundaryFrameAveraging

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.CurrentBoundaryShapeTransport
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable (M : NativeMeasuredSource F ζ hζ R P) (V : Level F ζ hζ)

def crossTest (φ : G F ζ hζ → ℂ)
    (z : KPMsFixedHaarDisintegration.Omega
      (nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V) × KPMsGreenFlux.K F) : ℂ :=
  ((cuspOffset F ζ hζ R P (nativeRecipe F ζ hζ R P) V z.1.1).val:ℂ)⁻¹ *
    φ (KPMsGreenFlux.compactInsertion F ζ hζ z.2 *
      (KPBoundedCuspFrames.actualFiniteRepresentative
        (nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V) z.1.1).val)

theorem crossTest_integrable (φ : G F ζ hζ → ℂ) (hφ : Continuous φ)
    (dk : Measure (KPMsGreenFlux.K F)) [IsFiniteMeasure dk] :
    Integrable (crossTest (R:=R) (P:=P) V φ) ((normalizedShapeBeta M V).prod dk) := by
  let A := nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V
  let J := KPMsFixedHaarDisintegration.CuspIndex A
  letI : TopologicalSpace J := ⊥
  letI : DiscreteTopology J := ⟨rfl⟩
  letI : CompactSpace KPCplxPrincipalSeriesCharts.compactSubgroup :=
    isCompact_iff_compactSpace.mp KPCplxPrincipalSeriesCharts.compactSubgroup_isCompact
  letI := normalizedShapeBeta_probability M V
  let H : J × KPMsGreenFlux.K F → ℂ := fun z =>
    ((cuspOffset F ζ hζ R P (nativeRecipe F ζ hζ R P) V z.1).val:ℂ)⁻¹ *
      φ (KPMsGreenFlux.compactInsertion F ζ hζ z.2 *
        (KPBoundedCuspFrames.actualFiniteRepresentative A z.1).val)
  have hc : Continuous H := by
    apply continuous_prod_of_discrete_left.mpr
    intro j
    dsimp only [H]
    apply Continuous.const_mul
    apply hφ.comp
    apply Continuous.mul_const
    change Continuous (fun k : KPMsGreenFlux.K F => KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (fun i => (k i).val))
    apply (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
    exact continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i))
  obtain ⟨b,hb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (J × KPMsGreenFlux.K F))).bddAbove_image hc.norm.continuousOn
  have hp : Continuous (fun ω : KPMsFixedHaarDisintegration.Omega A => (ω.1 : J)) :=
    continuous_sigma (fun _ => continuous_const)
  have hi : Integrable (fun z : KPMsFixedHaarDisintegration.Omega A × KPMsGreenFlux.K F => H (z.1.1,z.2))
      ((normalizedShapeBeta M V).prod dk) := by
    apply Integrable.of_bound (hc.comp ((hp.comp continuous_fst).prodMk continuous_snd)).aestronglyMeasurable b
    exact Filter.Eventually.of_forall (fun z => hb ⟨(z.1.1,z.2),Set.mem_univ _,rfl⟩)
  exact hi
end DedekindZetaZeroFree.CurrentBoundaryShapeTransport

end
