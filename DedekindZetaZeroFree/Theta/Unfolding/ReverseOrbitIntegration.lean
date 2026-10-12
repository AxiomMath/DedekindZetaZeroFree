module

public import DedekindZetaZeroFree.Theta.Unfolding.ReverseOrbitEvaluation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SignedExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem reverse_orbit_evaluation {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun ξ => ‖actualReflectedTerm R C v m Z ξ‖) ∧
    HasSum (actualReflectedTerm R C v m Z)
      (∑' i : OrbitIndex R, orbitTerm R C v m false Z hZ i) := by
  exact DedekindZetaZeroFree.OrbitExpansion.reverse_orbit_evaluation_clean R C hx v m Z hZ

end DedekindZetaZeroFree.ThetaExpansion.SignedExpansion

end
