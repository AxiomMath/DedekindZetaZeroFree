module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residual.UpperCompactWordExpansion

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open KPMsGreenFlux KPMsGreenFlux.IntrinsicAveraging KPSmoothActualFlowData
open KPContActualSphericalRightFieldIdentification KPMsClearedTruncationL2.NativeWordBridge
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
variable {hF : InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
set_option backward.isDefEq.respectTransparency false

theorem originalUpper_word (U : KPMsFixedHaarDisintegration.Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (j : Cusps A)
    (f : KPSmoothActualFlowData.X F ζ hζ → ℂ)
    (hf : ∀v, SmoothAutomorphic F ζ hζ (wordDerivative F ζ hζ v f))
    (h : Cover F ζ hζ → ℂ) (hh : ∀g, f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)=h g)
    (w : List (Fin (groupDimension F))) :
    actualRightWord F ζ hζ w (originalUpper R h) =
      originalUpper R (actualRightWord F ζ hζ w h) := by
  have he : h=IntrinsicAveraging.pullback f := (funext hh).symm
  rw [he]
  have hw : actualRightWord F ζ hζ w (IntrinsicAveraging.pullback f) =
      IntrinsicAveraging.pullback (wordDerivative F ζ hζ (w.map (wordIndexEquiv F)) f) := by
    funext g
    exact actualRightWord_eq_wordDerivative F ζ hζ w f g
  rw [hw]
  exact ResidualUpperWordInterchange.upper_word A (KPWildKernelUpperBound.quotientHaar F) j f hf w
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
