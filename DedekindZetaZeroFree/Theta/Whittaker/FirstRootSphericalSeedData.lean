module

public import DedekindZetaZeroFree.Theta.Profiles.FirstRootSphericalRadialModel

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

structure FirstRootSphericalSeed (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) where
  base : JointExteriorCoefficientSources R N
  neighborhood : ∀ p : R.A.Sf, Set (p.val.adicCompletion F)ˣ
  open_neighborhood : ∀ p, IsOpen (neighborhood p)
  one_neighborhood : ∀ p, (1 : (p.val.adicCompletion F)ˣ) ∈ neighborhood p
  spherical_near : ∀ v y, (∀ p, y.2 p ∈ neighborhood p) →
    fourier R base.sources.dq (base.realization.theta v) (diagonal R y) =
      firstRootSphericalProduct R y

end DedekindZetaZeroFree.ThetaExpansion

end
