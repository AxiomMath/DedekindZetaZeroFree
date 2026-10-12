module

public import DedekindZetaZeroFree.Theta.Periods.WeightedQuotientIntegrability

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField MeasureTheory
open DedekindZetaZeroFree.ThetaProfileHaarSheets DedekindZetaZeroFree.ThetaSheetExactUnfolding
namespace DedekindZetaZeroFree.ThetaExpansion.QuotientDescent
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem selected_theta_quotient_integrable
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R}
    (C : JointMellinGaussianSources R N)
    (hdesc : ∀ v m b (γ : R.A.Gamma) y,
      weightedDigits R C.sources C.realization C.packet v m b (γ.val * y) =
        weightedDigits R C.sources C.realization C.packet v m b y) :
    ∀ v m b l, letI := C.transport.groupHaar_isHaar;
      Integrable (quotientTheta R C.sources C.realization C.packet v m b l)
        (sheetQuotientHaar R.A C.packet.v₀ C.transport.groupHaar l) := by
  intro v m b l
  letI := C.transport.groupHaar_isHaar
  exact DedekindZetaZeroFree.DigitMasks.quotient_integrable_of_continuous_bdd_weight
    R.A C.packet.v₀ C.transport.groupHaar l
    (signedDigits R C.sources C.realization v m b)
    (DedekindZetaZeroFree.DigitMasks.thetaWeight R C.packet v)
    (quotientTheta R C.sources C.realization C.packet v m b l)
    (DedekindZetaZeroFree.DigitMasks.signedDigits_continuous R C.realization v m b)
    (DedekindZetaZeroFree.DigitMasks.thetaWeight_measurable R C.packet v)
    (DedekindZetaZeroFree.DigitMasks.thetaWeight_norm_le_one R C.packet v)
    (DedekindZetaZeroFree.DigitMasks.quotientTheta_projection R C.realization C.packet
      hdesc v m b l)
end DedekindZetaZeroFree.ThetaExpansion.QuotientDescent

end
