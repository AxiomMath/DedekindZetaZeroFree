module

public import DedekindZetaZeroFree.Adeles.Quotients.GreenIdentities.CompactInterior

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContCutoffLocalizedGreen

open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualCotangentCountableShrinking
open KPContCotangentOverlapRationalBranches KPContActualCotangentPieceHilbertSum
open KPContActualGlobalGreen

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

private lemma liftExtension_coordinates {F : Type} [Field F] [NumberField F] {ζ : F}
    {hζ : IsPrimitiveRoot ζ 12} {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
    (a : ShrunkChart F ζ hζ U R P H)
    (f : omega a → ℂ) (y : a.domain) :
    liftExtension a f (coordinates a y).val = f (coordinates a y) := by
  unfold liftExtension
  rw [dif_pos (coordinates a y).property]

theorem compact_interior_green
    (a : KPContActualCotangentCountableShrinking.ShrunkChart F ζ hζ U R P H)
    (w : KPContSectorSmoothFramesSupport.smoothSections F ζ hζ U R P H)
    (g : localScalarTests a)
    (hgcompact : HasCompactSupport (liftExtension a g.val))
    (hginterior : tsupport (liftExtension a g.val) ⊆ omega a) :
    (∫ y, sectionFields w.val a (coordinates a y) *
        star (HyperbolicChart.laplacian (KPContCotangentActualOverlap.d F)
          (liftExtension a g.val) (coordinates a y).val) ∂a.liftedMeasure) =
      ∫ y, HyperbolicChart.laplacian (KPContCotangentActualOverlap.d F)
          (liftExtension a (sectionFields w.val a)) (coordinates a y).val *
        star (g.val (coordinates a y)) ∂a.liftedMeasure := by
  have h := compact_interior_green_lift (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) a (sectionFields w.val)
    (smoothOnLift_sectionFields a w.val w.property) g hgcompact hginterior
  rw [show (∫ y, sectionFields w.val a (coordinates a y) *
        star (HyperbolicChart.laplacian (KPContCotangentActualOverlap.d F)
          (liftExtension a g.val) (coordinates a y).val) ∂a.liftedMeasure) =
      (∫ y, liftExtension a (sectionFields w.val a) (coordinates a y).val *
        star (HyperbolicChart.laplacian (KPContCotangentActualOverlap.d F)
          (liftExtension a g.val) (coordinates a y).val) ∂a.liftedMeasure) from
    integral_congr_ae (Filter.Eventually.of_forall fun y => by
      simp only [liftExtension_coordinates])]
  rw [show (∫ y, HyperbolicChart.laplacian (KPContCotangentActualOverlap.d F)
          (liftExtension a (sectionFields w.val a)) (coordinates a y).val *
        star (g.val (coordinates a y)) ∂a.liftedMeasure) =
      (∫ y, HyperbolicChart.laplacian (KPContCotangentActualOverlap.d F)
          (liftExtension a (sectionFields w.val a)) (coordinates a y).val *
        star (liftExtension a g.val (coordinates a y).val) ∂a.liftedMeasure) from
    integral_congr_ae (Filter.Eventually.of_forall fun y => by
      simp only [liftExtension_coordinates])]
  exact h

end DedekindZetaZeroFree.KPContCutoffLocalizedGreen

end
