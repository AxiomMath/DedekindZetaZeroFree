module

public import DedekindZetaZeroFree.Theta.Periods.FirstRootDifferentiation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical Topology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

structure FirstRootLift (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R)
    (J : FirstRootProjected R N A B) where
  base : JointExteriorCoefficientSources R N
  dq_exact : base.sources.dq = J.base.sources.dq
  residue_exact : ∀ v, base.realization.theta v =
    firstRootDerivatives R J.cutoffs (J.base.realization.theta v)

end DedekindZetaZeroFree.ThetaExpansion

end
