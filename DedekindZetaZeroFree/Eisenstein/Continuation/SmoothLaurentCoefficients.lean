module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarMeromorphicFamilies
public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothGermRestrictionAndTransport
public import DedekindZetaZeroFree.Eisenstein.Continuation.LaurentNumeratorCovariance
public import DedekindZetaZeroFree.Eisenstein.Continuation.LaurentCoefficientIdentificationAndSmoothness

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem selected_source_smooth_germ_of_scalar_germ
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R} (B : JointRootAlignedSources R N)
    (C : ScalarContinuation R B.sources) (v : R.A.UnitQuotient) (H : ScalarGerm C v) :
    ∃ G : IndividualSmoothGerm C v,
      G.radius ≤ H.radius ∧ ∀ s, s ∈ Metric.ball (0 : ℂ) G.radius →
        G.cleared s = (H.cleared s : Functions R) := by
  exact SmoothSource.selected_smooth_upgrade H
end DedekindZetaZeroFree.ThetaExpansion
