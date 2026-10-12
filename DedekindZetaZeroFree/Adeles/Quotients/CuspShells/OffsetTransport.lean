module

public import DedekindZetaZeroFree.MeasureTheory.Coarea.VariableOffsetRadialProducts
public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.FullAngularSupport

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal ENNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsNativeOffsetMass
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming nativeFullDomain → nativeFullDomain
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming nativeFrameInvariant → nativeFrameInvariant
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming actualFrame_spec → actualFrame_spec

theorem cuspOffset_right_center_cofinal
    (S : NativeRecipe F ζ hζ R P) (V : KPMsActualAngularSource.Level F ζ hζ)
    (j : NativeCusp F ζ hζ R P S V) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)) :
    KPMsAngularSourceRecipe.finiteOffset F ζ hζ
      (KPMsActualCuspSource.rationalLift F ζ hζ
        (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2))
      (((nativeAtlas F ζ hζ R P S V).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val) =
      cuspOffset F ζ hζ R P S V j :=
  FullSupportProof.finiteOffset_right_center_level S V _ _ ε u

theorem offset_shell_lintegral (d : ℕ) (hd : 0 < d)
    (c : ℝ) (hc : 0 < c) (Y : ℝ) (hY : 0 < Y) (a : ℝ≥0∞) :
    ENNReal.ofReal (2 * Y) *
      (∫⁻ t in Set.Ioi (Real.log (Y / c) / (2 * (d : ℝ))),
        if c * Real.exp (2 * (d : ℝ) * t) ≤ 2 * Y then a else 0
        ∂KPCuspCharts.radialMeasure d) =
      ENNReal.ofReal (c / (2 * (d : ℝ))) * a := by
  have hh := KPMsOffsetRadialCoarea.offset_radial_lintegral d hd c hc Y hY
    ((Set.Ioc Y (2 * Y)).indicator (fun _ => a))
  have hleft : (∫⁻ r in Set.Ioi Y, (Set.Ioc Y (2 * Y)).indicator (fun _ => a) r
      ∂KPMsFixedHaar.radialMeasure) = (ENNReal.ofReal (2 * Y))⁻¹ * a := by
    rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.mpr Set.Ioc_subset_Ioi_self, lintegral_const,
      Measure.restrict_apply_univ, KPMsFixedHaar.RadialIntegrationSteps.radial_shell Y hY,
      mul_comm]
    rw [ENNReal.ofReal_inv_of_pos (by positivity)]
  rw [hleft] at hh
  have htest : (∫⁻ t in Set.Ioi (Real.log (Y / c) / (2 * (d : ℝ))),
      (Set.Ioc Y (2 * Y)).indicator (fun _ => a) (c * Real.exp (2 * (d : ℝ) * t))
      ∂KPCuspCharts.radialMeasure d) =
      ∫⁻ t in Set.Ioi (Real.log (Y / c) / (2 * (d : ℝ))),
        if c * Real.exp (2 * (d : ℝ) * t) ≤ 2 * Y then a else 0
        ∂KPCuspCharts.radialMeasure d := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hr : Y < c * Real.exp (2 * (d : ℝ) * t) := by
      have hq : 0 < 2 * (d : ℝ) := by positivity
      have hl : Real.log (Y / c) < 2 * (d : ℝ) * t := by
        simpa only [mul_comm] using (div_lt_iff₀ hq).mp ht
      have he := Real.exp_lt_exp.mpr hl
      rw [Real.exp_log (div_pos hY hc)] at he
      simpa only [mul_comm] using (div_lt_iff₀ hc).mp he
    simp [Set.indicator, Set.mem_Ioc, hr]
  rw [htest] at hh
  rw [hh]
  have h2 : ENNReal.ofReal (2 * Y) ≠ 0 := by positivity
  rw [← mul_assoc, mul_comm (ENNReal.ofReal (2 * Y)), mul_assoc,
    ENNReal.mul_inv_cancel_left h2 ENNReal.ofReal_ne_top]

end DedekindZetaZeroFree.KPMsNativeOffsetMass

end
