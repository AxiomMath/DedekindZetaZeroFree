module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspAngles.TransitionsAndCoordinateDescent

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology NNReal ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsActualAngularCrossLevelFrameSource
open KPMsActualAngularSource KPMsActualAngularDescentSource KPMsActualAngularTransitionSource
open KPMsActualCuspSource KPMsActualAngularShellSource
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
local instance : MulAction (KPCuspArithmetic.PGL2 F) (KPArch.Space (KPCuspLogShape.dimension F)) :=
  KPCuspSiegel.instMulActionPGL2SpaceDimension F
 theorem frame_change_full_angular
    (D : Iwasawa F ζ hζ) (B B' : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (hslot : B.slot = B'.slot) (σ τ g h : KPMsActualAngularSource.G F ζ hζ)
    (y : Fˣ) (n : KPGlobalTorusFunctionData.Adeles F)
    (he : τ⁻¹ * h = (KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ n * (σ⁻¹ * g)) :
    framedFullAngular F ζ hζ D B' τ h = framedFullAngular F ζ hζ D B σ g := by
  have he' : σ⁻¹ * (σ * (τ⁻¹ * h)) =
      (KPGlobalTorusFunctionData.s F ζ hζ y).val *
        KPGlobalTorusFunctionData.N F ζ hζ n * (σ⁻¹ * g) := by
    simpa only [inv_mul_cancel_left] using he
  have hh := framedFullAngular_upper_transition F ζ hζ D B σ g (σ * (τ⁻¹ * h)) y n he'
  convert hh using 1
  unfold framedFullAngular framedNormOne framedNormalization
  congr 1
  apply Subtype.ext
  simp only [framedRadius, inv_mul_cancel_left, hslot]

 theorem all_level_radial_slot_eq
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U V : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    (H.disintegration U).radial.slot = (H.disintegration V).radial.slot := by
  let W : KPMsFixedHaarDisintegration.Level F ζ hζ :=
    ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup,
      U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩
  obtain ⟨CU⟩ := H.compatible W U inf_le_left
  obtain ⟨CV⟩ := H.compatible W V inf_le_right
  exact CU.common_slot.symm.trans CV.common_slot

 theorem framed_iwasawaNorm_eq_of_delta_one
    (D : Iwasawa F ζ hζ) (σ g h : KPMsActualAngularSource.G F ζ hζ)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (n : KPGlobalTorusFunctionData.Adeles F)
    (he : σ⁻¹ * h = t.val * KPGlobalTorusFunctionData.N F ζ hζ n * (σ⁻¹ * g))
    (ht : KPGlobalTorusFunctionData.delta F ζ hζ t = 1) :
    KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D (σ⁻¹ * h) =
      KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D (σ⁻¹ * g) := by
  rw [he, KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul, ht, one_mul]

end DedekindZetaZeroFree.KPMsActualAngularCrossLevelFrameSource

end
