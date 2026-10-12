module

public import DedekindZetaZeroFree.Theta.Periods.Cusps.BalancedFramesAndRayGeometry

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped Classical NumberField NNReal ENNReal Topology BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.CurrentBoundaryFrame
open KPMsGreenFlux KPContFlatArchDiagonalMultiplier KPMsActualAngularSource
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable (φ : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
variable (ha : ∀ (u : NumberField.InfinitePlace F → ℝ) g,
  φ ((aInfinity F ζ hζ u).val * g) =
    Complex.exp ((2:ℂ) * ((∑v, u v : ℝ):ℂ)) * φ g)
variable (hn : ∀ n g, φ (KPGlobalTorusFunctionData.N F ζ hζ n * g) = φ g)

private theorem radialSection_eq (w : NumberField.InfinitePlace F)
    (r : KPMsFixedHaarDisintegration.Radius) :
    KPMsFixedHaarDisintegration.radialSection F ζ hζ w r =
      (aInfinity F ζ hζ (fun v => if v = w then Real.log r.val / 2 else 0)).val := by
  change KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ _ =
    KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ _
  congr 1
  funext v
  by_cases hv : v = w
  · simp only [KPMsFixedHaarDisintegration.positiveSlots, hv, if_pos]
    rw [Real.exp_half, Real.exp_log r.property]
  · simp [KPMsFixedHaarDisintegration.positiveSlots,hv]

include ha in
theorem scalar_radial (w : NumberField.InfinitePlace F)
    (r : KPMsFixedHaarDisintegration.Radius) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    φ (KPMsFixedHaarDisintegration.radialSection F ζ hζ w r * g) = (r.val:ℂ)*φ g := by
  rw [radialSection_eq, ha]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_pos]
  rw [show (2:ℂ)*((Real.log r.val/2:ℝ):ℂ) = (Real.log r.val:ℂ) by push_cast; ring,
    ← Complex.ofReal_exp,Real.exp_log r.property]

include ha in
theorem scalar_normalization (D : Iwasawa F ζ hζ)
    (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ) (σ g : KPGlobalTorusFunctionData.G F ζ hζ) :
    φ (framedNormalization F ζ hζ D B σ g) =
      ((framedRadius F ζ hζ D σ g).val:ℂ)⁻¹ * φ (σ⁻¹*g) := by
  let r := framedRadius F ζ hζ D σ g
  have h := scalar_radial φ ha B.slot r (framedNormalization F ζ hζ D B σ g)
  simp only [framedNormalization, ← show framedRadius F ζ hζ D σ g = r from rfl,
    mul_inv_cancel_left] at h
  rw [h,← mul_assoc,inv_mul_cancel₀ (show (r.val:ℂ) ≠ 0 by exact_mod_cast r.property.ne'),one_mul]
  rfl

include ha hn in
theorem scalar_corrected_ray
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (j : Cusps A) (p : KPCuspCharts.Cross F) (k : K F)
    (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup) (r : ℝ) (hr : 0<r) :
    φ ((cuspRepresentative A j)⁻¹ * KPBoundedCuspFrames.actualCuspLift A j p k r *
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val.val) =
      (r:ℂ) * φ (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (fun i => (k i).val) *
        (KPBoundedCuspFrames.actualFiniteRepresentative A j).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val.val) := by
  unfold KPBoundedCuspFrames.actualCuspLift
  simp only [mul_assoc,inv_mul_cancel_left]
  rw [balanced_insertion_factor]
  simp only [mul_assoc]
  rw [hn,ha,heights_sum]
  have hcard : Fintype.card (NumberField.InfinitePlace F) = KPCuspLogShape.dimension F := by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,hF,zero_add]
  have hd := (KPCuspLogShape.dimension_pos F hF).ne'
  have hs : (Fintype.card (NumberField.InfinitePlace F):ℝ) *
      KPMsFixedHaarDisintegration.logHeight (F:=F) r = Real.log r / 2 := by
    rw [hcard,KPMsFixedHaarDisintegration.logHeight]
    field_simp
  rw [hs,show (2:ℂ)*((Real.log r/2:ℝ):ℂ) = (Real.log r:ℂ) by push_cast; ring,
    ← Complex.ofReal_exp,Real.exp_log hr]
end DedekindZetaZeroFree.CurrentBoundaryFrame

end
