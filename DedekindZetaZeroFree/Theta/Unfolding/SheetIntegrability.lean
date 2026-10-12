module

public import DedekindZetaZeroFree.Theta.Unfolding.SheetMultiplierMeasurability

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical ENNReal
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem sheet_digit_majorant_integrable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (i : OrbitIndex R) (l : PositiveAxis) :
    letI := C.transport.groupHaar_isHaar;
    Integrable (fun z : Sheet R.A l =>
      ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
        ‖digitWeight R m d * orbitFrequencyValue R C.sources C.realization v i
          (signedArgument R m b z.val d)‖)
      (pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l) := by
  letI := C.transport.groupHaar_isHaar
  exact integrable_finset_sum Finset.univ
    (fun d _ => C.absolute.orbit_sheet_integrable v m b i d l)

theorem orbitSheet_hasFiniteIntegral {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (i : OrbitIndex R) (l : PositiveAxis) :
    letI := C.transport.groupHaar_isHaar;
    HasFiniteIntegral (orbitSheet R C v m b i l)
      (pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l) := by
  letI := C.transport.groupHaar_isHaar
  have h := (sheet_digit_majorant_integrable R C v m b i l).hasFiniteIntegral
  exact h.mono (Filter.Eventually.of_forall (fun z =>
    (orbitSheet_norm_le R C v m b i l z).trans (le_abs_self _)))

theorem orbitSheet_integrable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (i : OrbitIndex R) (l : PositiveAxis) :
    letI := C.transport.groupHaar_isHaar;
    Integrable (orbitSheet R C v m b i l)
      (pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l) :=
  ⟨(orbitSheet_measurable R C v m b i l).aestronglyMeasurable,
    orbitSheet_hasFiniteIntegral R C v m b i l⟩

end DedekindZetaZeroFree.OrbitExpansion

end
