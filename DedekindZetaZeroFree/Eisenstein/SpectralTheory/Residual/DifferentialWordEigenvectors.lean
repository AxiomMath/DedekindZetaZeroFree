module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.MatrixFlowDerivativeIdentification
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.RightWordCommutation
public import DedekindZetaZeroFree.Eisenstein.Continuation.SphericalScalarPoleClearing

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy
open KPContActualSphericalRightFieldIdentification KPGlobalResidualConstruction KPLiteralChamber
open KPMsClearedTruncationL2.NativeWordBridge
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming word_smul → word_smul
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
 abbrev eigenvectorWordDerivative := KPSmoothActualFlowData.wordDerivative F ζ hζ

theorem original_word_eigen
    (f : KPSmoothActualFlowData.X F ζ hζ → ℂ)
    (hs : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (a * archChart F ζ hζ x)))
      (archDomain F))
    (eig : ℂ)
    (he : ∀ g, KPMsGreenFlux.casimir F ζ hζ
      (fun a => f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a)) g =
      eig * f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g))
    (w : List (KPSmoothActualFlowData.B F)) (g : KPSmoothActualFlowData.G F ζ hζ) :
    KPMsGreenFlux.casimir F ζ hζ
      (fun a => eigenvectorWordDerivative w f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a)) g =
      eig * eigenvectorWordDerivative w f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
  let W := w.map (wordIndexEquiv F).symm
  let up := fun a => f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a)
  have hW : W.map (wordIndexEquiv F) = w := by simp [W]
  have hw : actualRightWord F ζ hζ W up =
      fun a => eigenvectorWordDerivative w f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a) := by
    funext a
    rw [actualRightWord_eq_wordDerivative, hW]
  rw [← hw]
  rw [KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth.native_casimir_commutes_word up hs W g]
  have hE : KPMsGreenFlux.casimir F ζ hζ up = eig • up := funext he
  rw [hE, word_smul]
  change eig * actualRightWord F ζ hζ W up g = _
  rw [hw]

end DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy

end
