module

public import DedekindZetaZeroFree.Eisenstein.Continuation.FiniteWordResolventPoleSets

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms
open scoped Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem selected_scalar_pole_set_exists
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R} (B : JointRootAlignedSources R N)
    (v : R.A.UnitQuotient) (D : SelectedScalarBranch R B v) :
    Nonempty (SelectedPoleSet D) := by
  exact EisensteinSmoothGerms.ScalarSource.selected_pole_set R B v D

end DedekindZetaZeroFree.ThetaExpansion

end
