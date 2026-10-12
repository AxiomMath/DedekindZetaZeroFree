module

public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SignedExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def rowClass (u : R.A.Rˣ) : R.A.UnitQuotient :=
  QuotientGroup.mk (R.A.unitEquiv.symm u)

abbrev OrbitIndex := ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A

def orbitSheet {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (i : OrbitIndex R) (l : PositiveAxis) (z : Sheet R.A l) : ℂ :=
  (if QuotientGroup.mk' R.A.sixthPowers z.val ∈ R.probe.correction.B then 1 else 0) *
    (C.packet.branch v z.val)⁻¹ *
      ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
        digitWeight R m d * orbitFrequencyValue R C.sources C.realization v i
          (signedArgument R m b z.val d)

def orbitIntegral {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (i : OrbitIndex R) (l : PositiveAxis) : ℂ := by
  letI := C.transport.groupHaar_isHaar
  exact ∫ z, orbitSheet R C v m b i l z
    ∂pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l

def orbitTerm {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) (i : OrbitIndex R) : ℂ :=
  ∫ t : PositiveAxis, C.packet.kernel t.val *
    orbitIntegral R C v m b i ⟨t.val / Z, div_pos t.property hZ⟩ ∂positiveHaar

def AbsoluteExtraction {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N) : Prop :=
  ∀ (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z),
    (∀ i l, letI := C.transport.groupHaar_isHaar;
      Integrable (orbitSheet R C v m b i l)
        (pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l)) ∧
    (∀ i, Integrable (fun t : PositiveAxis => C.packet.kernel t.val *
      orbitIntegral R C v m b i ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar) ∧
    Summable (fun i : OrbitIndex R => ‖orbitTerm R C v m b Z hZ i‖) ∧
    HasSum (orbitTerm R C v m b Z hZ)
      (smoothedTheta R C.transport C.sources C.realization C.packet v m b Z -
        mainTerm R C.transport C.sources C.realization C.packet v m b Z) ∧
    Integrable (fun t : PositiveAxis => C.packet.kernel t.val *
      thetaAverage R C.transport C.sources C.realization C.packet v m b
        ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar

end DedekindZetaZeroFree.ThetaExpansion.SignedExpansion

end
