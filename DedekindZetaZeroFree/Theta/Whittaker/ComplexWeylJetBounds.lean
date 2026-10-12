module

public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SelectedWeylIdentification

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
open ThetaRawSheetEnvelope.WeightedWhittakerSheets
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem complex_weyl_jet_bounds (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) :
    ∀ A : ℝ, 0 < A → ∃ D : ℝ, 0 ≤ D ∧ ∀ v (w : InfinitePlace F)
      (j : ℕ), j ≤ 2 → ∀ z : w.Completionˣ,
      ‖localWeylArchJet R C v w j z‖ ≤
        D * archPowerMajorant A (‖(z : w.Completion)‖ ^ 2) := by
  intro A hA
  exact SheetRescaling.all_selected_arch_bounds_of_jacquet_identity R C
    (SheetRescaling.selected_weyl_jacquet_identity R C) A hA
end DedekindZetaZeroFree.ThetaExpansion

end
