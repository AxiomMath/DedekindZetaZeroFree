module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ActualNativeWordIdentification
public import DedekindZetaZeroFree.Eisenstein.Induction.SmoothSections.AutomorphicLift

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff
namespace DedekindZetaZeroFree.SharedSource
open KPGlobalResidualConstruction KPContSectorSmoothFramesSupport
open KPContActualCommonDiskRightHolomorphy
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeWordAction renaming actual_eq_word → actual_eq_word
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeWordAction renaming native_word_smooth → native_word_smooth
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming rightWord_continuous_of_chart_smooth → rightWord_continuous_of_chart_smooth
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming rightWord_level → rightWord_level
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming word_add → word_add
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming word_smul → word_smul
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem sectionLift_smooth
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (u : smoothSections F ζ hζ U R P H) :
    KPLiteralRaw.Smooth F ζ hζ (lift F ζ hζ U R P H u.val) :=
  ⟨ActualSectionLift.lift_continuous F ζ hζ U R P H u,
    ActualSectionLift.lift_arch_smooth F ζ hζ U R P H u,
    ActualSectionLift.nativeLevel F ζ hζ U,
    ActualSectionLift.lift_native_level F ζ hζ U R P H u.val⟩

theorem actualRightWord_smooth (u : KPLiteralRaw.Functions F ζ hζ)
    (hu : KPLiteralRaw.Smooth F ζ hζ u)
    (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))) :
    KPLiteralRaw.Smooth F ζ hζ
      (KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w u) := by
  obtain ⟨U, hU⟩ := hu.2.2
  obtain ⟨O, hOo, hb, hOD, hμ, hmaps, hprod, hthick, hcomm⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product F ζ hζ
  refine ⟨?_, native_word_smooth F ζ hζ u hu.2.1 w, U, ?_⟩
  · rw [actual_eq_word]
    exact rightWord_continuous_of_chart_smooth F ζ hζ U u hu.2.1
      (fun g a => hU g a.val a.property) _
  · intro g a ha
    rw [actual_eq_word]
    exact rightWord_level F ζ hζ u a (fun x => hcomm U a ha x)
      (fun g => hU g a ha) _ g

theorem actualRightWord_add (u v : KPLiteralRaw.Functions F ζ hζ)
    (hu : KPLiteralRaw.Smooth F ζ hζ u) (hv : KPLiteralRaw.Smooth F ζ hζ v)
    (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))) :
    KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w (u + v) =
      KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w u +
      KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w v := by
  simp_rw [actual_eq_word]
  exact word_add F ζ hζ u v hu.2.1 hv.2.1 _

theorem actualRightWord_smul (c : ℂ) (u : KPLiteralRaw.Functions F ζ hζ)
    (hu : KPLiteralRaw.Smooth F ζ hζ u)
    (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))) :
    KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w (c • u) =
      c • KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w u := by
  simp_rw [actual_eq_word]
  exact word_smul F ζ hζ c u hu.2.1 _

end DedekindZetaZeroFree.SharedSource

end
