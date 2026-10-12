module

public import DedekindZetaZeroFree.Theta.Periods.WeightedQuotientIntegrability

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources ThetaProfileHaarSheets ThetaSheetExactUnfolding
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def compactWeight {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (y : R.A.G) : ℂ :=
  (if QuotientGroup.mk' R.A.sixthPowers y ∈ R.probe.correction.B then 1 else 0) *
    (P.branch v y)⁻¹

theorem compactWeight_measurable {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) : Measurable (compactWeight R P v) := by
  exact thetaWeight_measurable R P v

theorem compactWeight_norm_le {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (y : R.A.G) : ‖compactWeight R P v y‖ ≤ 1 := by
  unfold compactWeight
  rw [norm_mul, norm_inv, branch_norm R P, inv_one, mul_one]
  split_ifs <;> simp

theorem sheet_out_eq_of_descent (A : SArithmeticData F) (l : PositiveAxis)
    (f : A.G → ℂ)
    (hdesc : ∀ (γ : A.Gamma) y, f (γ.val * y) = f y)
    (y : Sheet A l) : f (Quotient.out (sheetProjection A l y)).val = f y.val := by
  have he : sheetProjection A l (Quotient.out (sheetProjection A l y)) =
      sheetProjection A l y := Quotient.out_eq _
  have hr : MulAction.orbitRel A.Gamma1 (Sheet A l)
      (Quotient.out (sheetProjection A l y)) y := Quotient.exact he
  obtain ⟨γ, hγ⟩ := hr
  have hg : γ.val.val ∈ A.Gamma := γ.property
  have hv := congrArg Subtype.val hγ
  change γ.val.val * y.val = (Quotient.out (sheetProjection A l y)).val at hv
  rw [← hv]
  exact hdesc ⟨γ.val.val, hg⟩ y.val

end DedekindZetaZeroFree.DigitMasks

end
