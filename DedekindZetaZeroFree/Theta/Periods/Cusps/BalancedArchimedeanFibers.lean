module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspCutoffs.RadialJetFormula
public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.CoordinateMeasurability

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
namespace DedekindZetaZeroFree.CurrentBoundaryArchFiber
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsGreenFlux
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.GradientCollar renaming balancedArch_basepoint → balancedArch_basepoint
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FiniteSlabFullAngularHaar renaming compactSubgroup_eq_origin_stabilizer → compactSubgroup_eq_origin_stabilizer
open _root_.DedekindZetaZeroFree.KPContSectorArchSphericalFibers renaming mem_KInfinity_iff_stab → mem_KInfinity_iff_stab
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming actualFrame_spec → actualFrame_spec
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming nativeFullDomain → nativeFullDomain

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem arch_fiber_eq_balanced
    (σ : KPCuspArithmetic.PGL2 F) (a : KPSmoothActualFlowData.GInfinity F)
    (p : KPCuspCharts.Cross F) (t : ℝ)
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F σ (KPCuspCharts.toArch F (p,t))) :
    ∃ k : K F, a = KPMsActualCuspSource.archRational F σ *
      balancedArch (ζ := ζ) (hζ := hζ) p k
        (Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t)) := by
  let r := Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t)
  have hd : (2 * (KPCuspLogShape.dimension F : ℝ)) ≠ 0 := by
    have hp := KPCuspLogShape.dimension_pos F (NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by norm_num) hζ)
    positivity
  have hr : KPMsFixedHaarDisintegration.logHeight (F := F) r = t := by
    unfold KPMsFixedHaarDisintegration.logHeight r
    rw [Real.log_exp]
    exact mul_div_cancel_left₀ t hd
  let a₀ := KPMsActualCuspSource.archRational F σ *
    balancedArch (ζ := ζ) (hζ := hζ) p 1 r
  have hbase : KPMsFixedHaarDisintegration.archBasepoint F a₀ =
      KPMsFixedHaarDisintegration.archBasepoint F a := by
    dsimp only [a₀]
    rw [KPMsActualCuspSource.archBasepoint_rational_mul, balancedArch_basepoint, hr]
    exact ha.symm
  obtain ⟨κ,hκ⟩ :=
    (KPContSectorArchSphericalFibers.archBasepoint_eq_iff F a₀ a).mp hbase
  let k : K F := fun w => ⟨κ.val w, by
    rw [compactSubgroup_eq_origin_stabilizer]
    have hw := (mem_KInfinity_iff_stab F κ.val).mp κ.property
    have hi : KPCusp.complexPlace F
        (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w) = w :=
      (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ).left_inv w
    have hkw := hw (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)
    rw [hi] at hkw
    exact hkw⟩
  have hk : balancedArch (ζ := ζ) (hζ := hζ) p k r =
      balancedArch (ζ := ζ) (hζ := hζ) p 1 r * κ.val := by
    funext w
    simp only [balancedArch, Pi.mul_apply, Pi.one_apply, OneMemClass.coe_one, mul_one]
    rfl
  refine ⟨k, ?_⟩
  rw [hk, ← mul_assoc]
  exact hκ

end DedekindZetaZeroFree.CurrentBoundaryArchFiber

end
