module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteWeylCoefficientBounds
public import DedekindZetaZeroFree.Theta.Whittaker.ComplexWeylJetBounds
public import DedekindZetaZeroFree.Theta.Profiles.TensorProductWeylJetBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
open ThetaRawSheetEnvelope.WeightedWhittakerSheets
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem radial_sheet_jet_product_majorant (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) :
    ∀ A : ℝ, 0 < A → ∃ M D : ℝ, 0 < M ∧ 0 ≤ D ∧
      ∀ v κ (j : ℕ), j ≤ 2 → ∀ u : ℝ, ∀ y : R.A.G1,
        ‖iteratedDeriv j (fun t => radialSheetIntegrand R C v κ t y) u‖ ≤
          D * sheetProductPowerMajorant R M A
            (y.val * R.A.radialSection (Real.exp u) (Real.exp_pos u)) := by
  intro A hA
  obtain ⟨M, Df, hM, hDf, hf⟩ := finite_weyl_value_bounds R C
  obtain ⟨Da, hDa, ha⟩ := complex_weyl_jet_bounds R C A hA
  obtain ⟨Dt, hDt, ht⟩ := radial_sheet_jets_le_weyl_product_envelope R C
  let Cf := Df ^ Fintype.card R.A.Sf
  let Ca := (Fintype.card (InfinitePlace F → Fin 3) : ℝ) *
    Da ^ Fintype.card (InfinitePlace F)
  have hCf : 0 ≤ Cf := pow_nonneg hDf _
  have hCa : 0 ≤ Ca := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hDa _)
  have hfb (v : R.A.UnitQuotient) (z : R.A.G) :
      finiteWeylProductEnvelope R C v z ≤
        Cf * ∏ p : R.A.Sf, finitePowerMajorant M ‖(z.2 p : p.val.adicCompletion F)‖ := by
    calc
      _ ≤ ∏ p : R.A.Sf, Df * finitePowerMajorant M ‖(z.2 p : p.val.adicCompletion F)‖ :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun p _ => hf v p (z.2 p))
      _ = _ := by simp [Cf, Finset.prod_mul_distrib]
  have hab (v : R.A.UnitQuotient) (z : R.A.G) :
      archWeylJetProductEnvelope R C v z ≤
        Ca * ∏ w : InfinitePlace F, archPowerMajorant A (‖(z.1 w : w.Completion)‖ ^ 2) := by
    calc
      _ ≤ ∑ a : InfinitePlace F → Fin 3,
          ∏ w : InfinitePlace F, Da * archPowerMajorant A (‖(z.1 w : w.Completion)‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro a _
        exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun w _ => ha v w (a w).val (by omega) (z.1 w))
      _ = _ := by simp [Ca, Finset.prod_mul_distrib]; ring
  refine ⟨M, Dt * (Cf * Ca), hM, mul_nonneg hDt (mul_nonneg hCf hCa), ?_⟩
  intro v κ j hj u y
  let z := y.val * R.A.radialSection (Real.exp u) (Real.exp_pos u)
  have hprod := mul_le_mul (hfb v z) (hab v z)
    (Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (mul_nonneg hCf (Finset.prod_nonneg fun p _ =>
      finitePowerMajorant_nonneg M _ (norm_nonneg _)))
  calc
    _ ≤ Dt * (finiteWeylProductEnvelope R C v z * archWeylJetProductEnvelope R C v z) :=
      ht v κ j hj u y
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod hDt
    _ = _ := by dsimp [sheetProductPowerMajorant, z]; ring
end DedekindZetaZeroFree.ThetaExpansion

end
