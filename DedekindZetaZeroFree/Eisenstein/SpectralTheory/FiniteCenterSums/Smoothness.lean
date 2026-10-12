module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteCenterSums.QuotientRealization
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightWordFiniteSums

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
open ResidualSphericalGeometry ResidualWeakEnergy KPGlobalResidualConstruction
open KPMsClearedTruncationL2.NativeWordBridge
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (M : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable {n : ℕ} (U : Fin n → KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (m : Fin n → ℕ)
variable (w : ∀ i, Fin (m i) → List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))
variable (a : ∀ i, Fin (m i) → ℂ)
variable (Z : ∀ i, Fin (m i) → KPContActualAllCuspSource.SmoothSections F ζ hζ M R P H (U i))
 abbrev rawSmoothWordDerivative := KPSmoothActualFlowData.wordDerivative F ζ hζ

open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_smul → smooth_smul

theorem finiteCenterSum_raw_smooth : KPLiteralRaw.Smooth F ζ hζ (fun g =>
    finiteCenterSum F ζ hζ M R P H U m w a Z
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) := by
  have he : (fun g => finiteCenterSum F ζ hζ M R P H U m w a Z
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) =
      ∑ i, ∑ j, a i j • KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ
        (w i j) (KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ M R P H (U i) (Z i j)) := by
    funext g
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      finiteCenterSum_lift F ζ hζ M R P H U m w a Z g
  rw [he]
  apply SharedSource.nativeSmooth_finset_sum
  intro i hi
  apply SharedSource.nativeSmooth_finset_sum
  intro j hj
  apply smooth_smul F ζ hζ
  apply SharedSource.actualRightWord_smooth
  exact SharedSource.sectionLift_smooth
    (KPContActualAllCuspSource.level F ζ hζ M R P H (U i)) R P H (Z i j)

theorem finiteCenterSum_word_raw_smooth (v : List (KPSmoothActualFlowData.B F)) :
    KPLiteralRaw.Smooth F ζ hζ (fun g => rawSmoothWordDerivative F ζ hζ v
      (finiteCenterSum F ζ hζ M R P H U m w a Z)
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) := by
  let W := v.map (wordIndexEquiv F).symm
  have hW : W.map (wordIndexEquiv F) = v := by simp [W]
  have hh := SharedSource.actualRightWord_smooth _
    (finiteCenterSum_raw_smooth F ζ hζ M R P H U m w a Z) W
  have he : KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ W
      (fun g => finiteCenterSum F ζ hζ M R P H U m w a Z
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) =
      fun g => rawSmoothWordDerivative F ζ hζ v (finiteCenterSum F ζ hζ M R P H U m w a Z)
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
    funext g
    rw [actualRightWord_eq_wordDerivative, hW]
  rwa [he] at hh

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
