module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.ScalarRealization

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualSphericalGeometry
open KPContSectorCoveredQuotientVocabulary KPContSectorSmoothFramesSupport
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (V : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

theorem originalScalar_KU_fixed (Z : smoothSections F ζ hζ V R P H)
    (k : K_U F ζ hζ V) (x : KPSmoothActualFlowData.X F ζ hζ) :
    originalScalar F ζ hζ V R P H Z
      (KPSmoothActualFlowData.rightTranslate F ζ hζ k.val x) =
      originalScalar F ζ hζ V R P H Z x := by
  induction x using Quotient.inductionOn with
  | h g =>
    change ((smoothS F ζ hζ V R P H).symm Z).val.val
      (KPContSectorQuotientRelationsComparison.e F ζ hζ V
        (DoubleCoset.mk (Gamma F ζ hζ) (K_U F ζ hζ V) (g*k.val))) =
      ((smoothS F ζ hζ V R P H).symm Z).val.val
        (KPContSectorQuotientRelationsComparison.e F ζ hζ V
          (DoubleCoset.mk (Gamma F ζ hζ) (K_U F ζ hζ V) g))
    rw [DoubleCoset.mk_mul_mem k g]

end DedekindZetaZeroFree.FourierContinuation.ResidualSphericalGeometry

end
