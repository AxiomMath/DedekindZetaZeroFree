module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Eigenfunctions.DiagonalEnergy

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy
open KPMsClearedTruncationL2
open _root_.DedekindZetaZeroFree.FourierContinuation.ResidualCompactSecondL2 renaming compactAction → compactAction
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalWordRegularity renaming word_mem_smoothSpace → word_mem_smoothSpace
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
 abbrev integrableEigenfunctionWordDerivative := KPSmoothActualFlowData.wordDerivative F ζ hζ

theorem eigen_all_word_memLp
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    {U₀ : Level F ζ hζ} (f : smoothSpace F ζ hζ U₀)
    (eig : ℂ) (he : ∀ w g, KPMsGreenFlux.casimir F ζ hζ
      (fun a => integrableEigenfunctionWordDerivative w f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a)) g =
      eig * integrableEigenfunctionWordDerivative w f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g))
    (hf : MemLp f.val 2 R.quotientHaar)
    (hk : ∀ w, FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range (fun k : KPMsGreenFlux.K F => (integrableEigenfunctionWordDerivative w f.val) ∘ compactAction k)))) :
    ∀ w, MemLp (integrableEigenfunctionWordDerivative w f.val) 2 R.quotientHaar := by
  intro w
  induction w with
  | nil => exact hf
  | cons b w ih =>
    let fw : smoothSpace F ζ hζ U₀ := ⟨integrableEigenfunctionWordDerivative w f.val, word_mem_smoothSpace f w⟩
    letI := hk w
    exact eigen_first_derivative_memLp A R P D Y hY fw eig (he w) ih b

end DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy

end
