module

public import DedekindZetaZeroFree.Eisenstein.Continuation.MovingCharts.LocalExponentialInverse
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ActualNativeWordIdentification
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactWordNumerator

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology ContDiff BigOperators
open Filter MeasureTheory
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.ResidueAutomorphy.NativeArchSmooth
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_line_construction → scalar_line_construction
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_analytic_of_right_holomorphic → scalar_analytic_of_right_holomorphic
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming word_smul → word_smul
open _root_.DedekindZetaZeroFree.KPContinuation.NativeWordCompactHolomorphy renaming actualRightWord_compact_holomorphy → actualRightWord_compact_holomorphy
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming word_zero → word_zero
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming literal_finite_word_chamber → literal_finite_word_chamber

open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming scalar_eq_lift → scalar_eq_lift
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeWordAction renaming native_word_smooth → native_word_smooth
open _root_.DedekindZetaZeroFree.KPContActualCutoffPlusClearedGerm.ChartSeriesBridge renaming tensor_lifted_smooth → tensor_lifted_smooth
open _root_.DedekindZetaZeroFree.KPContActualCommonDiskRightHolomorphy renaming level_projection → level_projection
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

private theorem lift_arch_smooth
    (V : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (u : KPContSectorSmoothFramesSupport.smoothSections F ζ hζ V R P H)
    (g : KPLiteralRaw.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => KPContActualCommonDiskRightHolomorphy.lift F ζ hζ V R P H u.val
        (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archDomain F) := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨e, he, Q, W, hWo, hpx, hWd, τ, hτ, hτ0, hτc, hτQ, hτsm, hτj, hprod⟩ :=
    KPGlobalResidualConstruction.ActualMovingLocal.moving_inverse_local
      F ζ hζ V R P H g x hx
  let A : Set (KPGlobalResidualConstruction.ArchCoordinates F) := {y | (g,y) ∈ W}
  have hAo : IsOpen A := hWo.preimage (continuous_const.prodMk continuous_id)
  refine ⟨A, hAo, hpx, ?_⟩
  have hsm := (tensor_lifted_smooth Q u).comp (hτsm g) (fun y hy => hτQ hy)
  apply (hsm.congr (fun y hy => ?_)).mono Set.inter_subset_right
  obtain ⟨v, hv⟩ := hprod (g,y) hy
  rw [hv]
  unfold KPContActualCommonDiskRightHolomorphy.lift
  rw [level_projection F ζ hζ V v]
  rfl

 theorem groupScalar_word_arch_smooth
    (u : KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U)
    (w : List (Fin (groupDimension F))) :
    ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U u)
        (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archDomain F) := by
  rw [scalar_eq_lift F ζ hζ C R P H U u]
  exact native_word_smooth F ζ hζ _
    (lift_arch_smooth F ζ hζ R P H
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) u) w

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.ResidueAutomorphy.NativeArchSmooth

end
