module

public import DedekindZetaZeroFree.Theta.Profiles.RadialJetsAndLocalNorms
public import DedekindZetaZeroFree.Theta.Profiles.ProductSheetIntegralBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem sheet_product_power_majorant_integrals (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (_C : JointDigitDescentSources R N)
    (σ : ℝ) (hσ : -(1 / 4 : ℝ) < σ) (A : ℝ) (hA : max σ 0 < A)
    (M : ℝ) (hM : 0 < M) :
    letI : MeasurableSpace R.A.G1 := borel _;
    (∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ,
      Integrable (fun y : R.A.G1 => sheetProductPowerMajorant R M A
        (y.val * R.A.radialSection (Real.exp u) (Real.exp_pos u))) R.probe.domain.measure ∧
      (∫ y : R.A.G1, sheetProductPowerMajorant R M A
        (y.val * R.A.radialSection (Real.exp u) (Real.exp_pos u))
          ∂ R.probe.domain.measure) ≤ K * Real.exp (-σ * u)) ∧
    (∀ u : ℝ, ∃ s ∈ nhds u, ∃ E : R.A.G1 → ℝ,
      Integrable E R.probe.domain.measure ∧ ∀ᵐ y ∂ R.probe.domain.measure,
        ∀ t ∈ s, sheetProductPowerMajorant R M A
          (y.val * R.A.radialSection (Real.exp t) (Real.exp_pos t)) ≤ E y) := by
  exact SheetRescaling.product_sheet_integrals R N σ hσ A hA M hM
end DedekindZetaZeroFree.ThetaExpansion

end
