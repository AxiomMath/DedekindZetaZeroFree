module

public import DedekindZetaZeroFree.Theta.Periods.CompactDigitContinuity
public import DedekindZetaZeroFree.Theta.Digits.CompactQuotientWeights

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField MeasureTheory
open DedekindZetaZeroFree.ThetaProfileHaarSheets DedekindZetaZeroFree.ThetaSheetExactUnfolding
namespace DedekindZetaZeroFree.ThetaExpansion.QuotientDescent
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem selected_upper_quotient_integrable
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R}
    (C : JointMellinGaussianSources R N)
    (hdesc : ∀ v m b (γ : R.A.Gamma) y,
      weightedUpper R C.sources C.realization C.packet v m b (γ.val * y) =
        weightedUpper R C.sources C.realization C.packet v m b y) :
    ∀ v m b l, letI := C.transport.groupHaar_isHaar;
      Integrable (quotientUpper R C.sources C.realization C.packet v m b l)
        (sheetQuotientHaar R.A C.packet.v₀ C.transport.groupHaar l) := by
  intro v m b l
  letI := C.transport.groupHaar_isHaar
  apply DedekindZetaZeroFree.DigitMasks.quotient_integrable_of_continuous_bdd_weight
    R.A C.packet.v₀ C.transport.groupHaar l
    (upperDigits R C.sources C.realization v m b)
    (DedekindZetaZeroFree.DigitMasks.compactWeight R C.packet v)
    (quotientUpper R C.sources C.realization C.packet v m b l)
    (DedekindZetaZeroFree.DigitMasks.upperDigits_continuous R C.realization v m b)
    (DedekindZetaZeroFree.DigitMasks.compactWeight_measurable R C.packet v)
    (DedekindZetaZeroFree.DigitMasks.compactWeight_norm_le R C.packet v)
  intro y
  change weightedUpper R C.sources C.realization C.packet v m b
    (Quotient.out (sheetProjection R.A l y)).val = _
  rw [DedekindZetaZeroFree.DigitMasks.sheet_out_eq_of_descent R.A l
    (weightedUpper R C.sources C.realization C.packet v m b) (hdesc v m b)]
  rfl
end DedekindZetaZeroFree.ThetaExpansion.QuotientDescent

end
