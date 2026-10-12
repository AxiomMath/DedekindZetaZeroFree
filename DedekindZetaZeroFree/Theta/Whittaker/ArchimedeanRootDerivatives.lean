module

public import DedekindZetaZeroFree.Theta.Profiles.FirstRootSphericalRadialModel

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def firstRootLocalDerivative (R : PrincipalMellin.ActualRecipe S η)
    (w : InfinitePlace F) (e : ℤ) (f : Functions R) : Functions R :=
  (Complex.I * (4 * Real.pi : ℂ))⁻¹ •
    (upperLieDerivative R w false f +
      (if e = 1 then -Complex.I else Complex.I) • upperLieDerivative R w true f)

def firstRootDerivatives (R : PrincipalMellin.ActualRecipe S η)
    (B : FirstRootCutoffs R) (f : Functions R) : Functions R :=
  (Finset.univ : Finset (InfinitePlace F)).toList.foldr
    (fun w h => firstRootLocalDerivative R w (B.exponent w) h) f

end DedekindZetaZeroFree.ThetaExpansion

end
