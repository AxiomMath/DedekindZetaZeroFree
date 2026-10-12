module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteWeylUniformBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
open ThetaRawSheetEnvelope.WeightedWhittakerSheets
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem finite_weyl_value_bounds (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) :
    ∃ M D : ℝ, 0 < M ∧ 0 ≤ D ∧ ∀ v (p : R.A.Sf) (z : (p.val.adicCompletion F)ˣ),
      ‖normalizedLocalWeylValue R C v (Sum.inr p.val) z‖ ≤
        D * finitePowerMajorant M ‖(z : p.val.adicCompletion F)‖ := by
  exact SheetRescaling.finite_weyl_bounds R C
end DedekindZetaZeroFree.ThetaExpansion

end
