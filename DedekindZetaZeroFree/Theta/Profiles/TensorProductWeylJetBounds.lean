module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.WeylFactorization

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def archWeylJetProductEnvelope (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) (v : R.A.UnitQuotient) (y : R.A.G) : ℝ :=
  ∑ a : InfinitePlace F → Fin 3,
    ∏ w : InfinitePlace F, ‖localWeylArchJet R C v w (a w).val (y.1 w)‖

def finiteWeylProductEnvelope (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) (v : R.A.UnitQuotient) (y : R.A.G) : ℝ :=
  ∏ p : R.A.Sf, ‖normalizedLocalWeylValue R C v (Sum.inr p.val) (y.2 p)‖

theorem radial_sheet_jets_le_weyl_product_envelope (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ v κ (j : ℕ), j ≤ 2 → ∀ u : ℝ, ∀ y : R.A.G1,
      let z := y.val * R.A.radialSection (Real.exp u) (Real.exp_pos u);
      ‖iteratedDeriv j (fun t => radialSheetIntegrand R C v κ t y) u‖ ≤
        D * (finiteWeylProductEnvelope R C v z * archWeylJetProductEnvelope R C v z) := by
  simpa only [finiteWeylProductEnvelope, archWeylJetProductEnvelope] using
    SheetRescaling.WeylTensorTransport.radial_transport R C
end DedekindZetaZeroFree.ThetaExpansion

end
