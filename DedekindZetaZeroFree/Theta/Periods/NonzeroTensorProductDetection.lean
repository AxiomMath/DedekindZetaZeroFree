module

public import DedekindZetaZeroFree.Theta.Periods.RankOne.ComplexSliceSpans
public import DedekindZetaZeroFree.Theta.Periods.RankOne.FiniteSliceSpans
public import DedekindZetaZeroFree.Theta.Periods.TensorRealization.ExteriorSphericalVectors
public import DedekindZetaZeroFree.Theta.Periods.TensorRealization.HarishChandraHeckeGeneration
public import DedekindZetaZeroFree.Theta.Periods.TensorRealization.LocalAndSU2Actions
public import DedekindZetaZeroFree.Theta.Periods.TensorRealization.NonzeroTraceDetection
public import DedekindZetaZeroFree.Theta.Periods.TensorRealization.ScalarCore

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end DedekindZetaZeroFree.ThetaExpansion

section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem detected_period_factorization
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (prior : Nonempty (JointRealizedFlatSources R N)) :
    Nonempty (JointHaarFactorizedSources R N) := by
  have h1 := tensorSeed_nonempty  R hR N prior
  have h2 := tensorHC_nonempty  R hR N h1
  have h3 := tensorActions_nonempty  R hR N h2
  have h4 := tensorDetected_nonempty  R hR N h3
  have h5 := tensorSpherical_nonempty  R hR N h4
  have h6 := tensorFiniteLines_nonempty  R hR N h5
  obtain ⟨D⟩ := tensorLocalLines_nonempty  R hR N h6
  exact ⟨FourierContinuation.jointHaarFactorizedSources_of_factorization D.toJointRealizedFlatSources D.factorization⟩
end DedekindZetaZeroFree.ThetaExpansion

end
