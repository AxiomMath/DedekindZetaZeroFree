module

public import DedekindZetaZeroFree.Theta.Unfolding.GroupedForwardOrbitEvaluation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SignedExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem forward_orbit_evaluation {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (u : R.A.Rˣ) (h d : R.A.Exterior)
    (hh : Powerful h.val) (hd : Squarefree d.val) (hc : h.val ⊔ d.val = ⊤)
    (Z : ℝ) (hZ : 0 < Z) :
    HasSum (orbitTerm R C (rowClass R u)
      (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) true Z hZ)
      (ThetaReflectionData.forwardB R.A R.probe.coefficients
        (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) Z) := by
  exact DedekindZetaZeroFree.OrbitExpansion.forward_orbit_evaluation R C hx u h d hh hd hc Z hZ

end DedekindZetaZeroFree.ThetaExpansion.SignedExpansion

end
